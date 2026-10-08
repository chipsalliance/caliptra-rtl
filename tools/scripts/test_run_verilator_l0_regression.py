# SPDX-License-Identifier: Apache-2.0
#
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

"""Regression runner tests."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest
from unittest.mock import patch

import yaml

import run_verilator_l0_regression as runner


class RegressionRunnerTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.manifest = self.root / "manifest.yml"
        self.paths = []

    def add_test(self, variant, testname="shared_firmware", parent="shared_firmware", **fields):
        path = self.root / parent / (variant + ".yml")
        path.parent.mkdir(exist_ok=True)
        path.write_text(yaml.safe_dump({"testname": testname, **fields}))
        self.paths.append(str(path.relative_to(self.root)))
        return path

    def save_manifest(self):
        self.manifest.write_text(yaml.safe_dump({"contents": [{"tests": {"paths": self.paths}}]}))
        return self.manifest

    def test_yaml_variant_names_firmware_plusargs_and_seed(self):
        self.add_test("outputs", plusargs=["+CLP_DCLS_EN", "+CALIPTRA_TEST_DCLS=outputs"], seed=1)
        self.add_test("control", plusargs=["+CLP_DCLS_DIS", "+CALIPTRA_TEST_DCLS=control"], seed="${PLAYBOOK_RANDOM_SEED}")
        with patch.dict(os.environ, {"PLAYBOOK_RANDOM_SEED": "42"}):
            tests = runner.load_tests(self.save_manifest(), 7)
        self.assertEqual([test.testname for test in tests], ["shared_firmware"] * 2)
        self.assertEqual([test.seed for test in tests], [1, 42])
        self.assertEqual(tests[1].plusargs, ("+CLP_DCLS_DIS", "+CALIPTRA_TEST_DCLS=control"))
        self.assertNotEqual(tests[0].identity, tests[1].identity)

    def test_manifest_resolves_paths_and_reads_all_groups(self):
        self.add_test("first", testname="firmware_a")
        second = self.add_test("second", testname="firmware_b")
        self.manifest.write_text(yaml.safe_dump({"contents": [
            {"tests": {"paths": [self.paths[0]]}},
            {"tests": {"paths": ["${TEST_CONFIG_ROOT}/" + second.name]}}]}))
        with patch.dict(os.environ, {"TEST_CONFIG_ROOT": str(second.parent)}):
            tests = runner.load_tests(self.manifest, 7)
        self.assertEqual([test.testname for test in tests], ["firmware_a", "firmware_b"])
        self.assertEqual(tests[0].plusargs, ())

    def test_default_manifest_and_cli_profile_selection(self):
        self.assertEqual(runner.parse_args([]).subsystem, 0)
        self.assertEqual(runner.parse_args(["--subsystem", "1", "--manifest", "custom.yml"]).manifest,
                         Path("custom.yml"))
        self.assertEqual(runner.default_manifest(self.root, 0).name, "L0_regression.yml")
        self.assertEqual(runner.default_manifest(self.root, 1).name, "L0_ss_mode_regression.yml")
        with patch.dict(os.environ, {"CALIPTRA_ROOT": str(self.root)}):
            test = runner.RegressionTest("variant", "firmware", ("+CLP_DCLS_EN",), 9)
            for profile in (0, 1):
                build = runner.make_command(self.root, profile, "verilator-build")
                run = runner.make_command(self.root, profile, "verilator", test)
                self.assertIn(f"CALIPTRA_MODE_SUBSYSTEM={profile}", build)
                self.assertIn(f"CALIPTRA_MODE_SUBSYSTEM={profile}", run)
                self.assertIn("TESTNAME=firmware", run)
                self.assertIn("PLAYBOOK_RANDOM_SEED=9", run)
                self.assertIn("RUN_PLUSARGS=+CLP_DCLS_EN", run)

    def test_invalid_configuration_and_conflicting_dcls_fail(self):
        invalid = [
            {"plusargs": "+CLP_DCLS_EN"},
            {"plusargs": [123]},
            {"plusargs": ["+CLP_DCLS_EN", "+CLP_DCLS_DIS"]},
            {"plusargs": ["+ONE +TWO"]},
            {"seed": "unresolved_seed"},
            {"simulators": "vcs"},
        ]
        for fields in invalid:
            with self.subTest(fields=fields):
                self.paths = []
                self.add_test("bad", **fields)
                with self.assertRaises(ValueError):
                    runner.load_tests(self.save_manifest(), 7)
        self.paths = ["missing.yml"]
        with self.assertRaises(FileNotFoundError):
            runner.load_tests(self.save_manifest(), 7)
        self.manifest.write_text("contents: {}")
        with self.assertRaises(ValueError):
            runner.load_tests(self.manifest, 7)

    def test_duplicates_rejected_and_unsupported_tests_are_not_passed(self):
        self.add_test("smoke", testname="smoke_firmware")
        self.add_test("requires_vcs", simulators=["vcs"])
        self.add_test("clock_gating", testname="smoke_test_clk_gating", parent="smoke_test_clk_gating")
        with self.assertLogs(runner.logger, level="INFO") as logged:
            tests = runner.load_tests(self.save_manifest(), 7)
        self.assertEqual([test.testname for test in tests], ["smoke_firmware"])
        self.assertTrue(any("Not run by Verilator" in line and "requires vcs" in line for line in logged.output))
        self.paths = [self.paths[0], self.paths[0]]
        with self.assertRaises(ValueError):
            runner.load_tests(self.save_manifest(), 7)

    def test_existing_exclusions_cover_aliased_firmware_and_variant_paths(self):
        self.add_test("smoke", testname="smoke_firmware")
        self.add_test("smoke_test_kv_cg", testname="smoke_test_kv_uds_reset", parent="smoke_test_kv_cg")
        parent = self.root / "smoke_test_dma_alias"
        parent.mkdir()
        alias = parent / "ordinary_variant.yml"
        alias.write_text(yaml.safe_dump({"testname": "ordinary_firmware"}))
        self.paths.append(str(alias.relative_to(self.root)))
        tests = runner.load_tests(self.save_manifest(), 7)
        self.assertEqual([test.testname for test in tests], ["smoke_firmware"])

    def test_make_recipe_roundtrip_does_not_execute_plusarg_contents(self):
        # Check plusarg quoting through make and its recipe shell.
        scripts = self.root / "tools/scripts"
        scripts.mkdir(parents=True)
        capture = self.root / "capture.py"
        capture.write_text("import json, sys; print(json.dumps(sys.argv[1:]))\n")
        (scripts / "Makefile").write_text("verilator:\n\tpython3 capture.py $(RUN_PLUSARGS)\n")
        marker = self.root / "should_not_exist"
        args = ("+CLP_DCLS_EN", "+TEXT=two words", "+PAYLOAD=$(touch " + str(marker) + ")",
                "+BACKTICK=`touch " + str(marker) + "`", "+SEMICOLON=;touch " + str(marker))
        test = runner.RegressionTest("variant", "firmware", args, 1)
        with patch.dict(os.environ, {"CALIPTRA_ROOT": str(self.root)}):
            command = runner.make_command(self.root, 1, "verilator", test)
            result = subprocess.run(command, universal_newlines=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        line = next(line for line in result.stdout.splitlines() if line.startswith("["))
        self.assertEqual(tuple(json.loads(line)), args)
        self.assertFalse(marker.exists())

    def test_variants_use_independent_build_directories_and_pending_slots(self):
        pristine = self.root / "pristine"
        pristine.mkdir()
        (pristine / "obj_dir").mkdir()
        (pristine / "obj_dir/Vcaliptra_top_tb").write_text("native model")
        (pristine / "verilator-build").touch()
        first = runner.RegressionTest("outputs", "shared_firmware", ("+MODE=outputs",), 1)
        second = runner.RegressionTest("regfile", "shared_firmware", ("+MODE=regfile",), 1)
        pending = [1, 1]
        runner.init_pool(threading.Lock(), pending)
        with patch.dict(os.environ, {"CALIPTRA_ROOT": str(self.root)}), \
                patch.object(runner, "runBashScript", return_value=(0, b"* TESTCASE PASSED", b"")) as command:
            self.assertEqual(runner.runTest((first, str(self.root), str(pristine), 0, 1)), 0)
            self.assertEqual(runner.runTest((second, str(self.root), str(pristine), 1, 1)), 0)
        self.assertTrue((self.root / "outputs/verilator-build").exists())
        self.assertTrue((self.root / "regfile/verilator-build").exists())
        self.assertEqual(pending, [0, 0])
        self.assertIn("RUN_PLUSARGS=+MODE=outputs", command.call_args_list[0][0][0])
        self.assertIn("RUN_PLUSARGS=+MODE=regfile", command.call_args_list[1][0][0])

    def test_missing_or_contradictory_pass_evidence_fails(self):
        self.assertTrue(runner.simulation_passed(0, "* TESTCASE PASSED"))
        self.assertFalse(runner.simulation_passed(1, "* TESTCASE PASSED"))
        self.assertFalse(runner.simulation_passed(0, "simulation completed"))
        self.assertFalse(runner.simulation_passed(0, "* TESTCASE PASSED\n* TESTCASE FAILED"))
        self.assertFalse(runner.simulation_passed(0, "SVA ERROR: assertion failed\n* TESTCASE PASSED"))
        self.assertTrue(runner.simulation_passed(0, "ERROR: expected negative-case diagnostic\n* TESTCASE PASSED"))


if __name__ == "__main__":
    unittest.main()
