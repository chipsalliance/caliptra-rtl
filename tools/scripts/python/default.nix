# SPDX-License-Identifier: Apache-2.0
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
{
  inputs,
  pkgs,
  python313,
  lib,
  ...
}: let
  mkEnv = python: let
    workspace = inputs.uv2nix.lib.workspace.loadWorkspace {
      workspaceRoot = ./.;
    };
    overlay = workspace.mkPyprojectOverlay {
      sourcePreference = "wheel";
    };

    # Sdist-only packages on PyPI: inject setuptools/wheel as build inputs.
    # `[tool.uv.extra-build-dependencies]` in pyproject.toml is uv-only and
    # is not seen by the hermetic per-sdist derivations uv2nix produces.
    sdistBuildDeps = final: prev: let
      addBuildDeps = deps: pkg:
        pkg.overrideAttrs (old: {
          nativeBuildInputs = (old.nativeBuildInputs or []) ++ deps;
        });
    in {
      peakrdl-uvm = addBuildDeps [final.setuptools final.wheel] prev.peakrdl-uvm;
      peakrdl-html = addBuildDeps [final.setuptools final.wheel] prev.peakrdl-html;
      systemrdl-compiler = addBuildDeps [final.setuptools final.wheel] prev.systemrdl-compiler;
    };

    pythonSet =
      (pkgs.callPackage inputs.pyproject-nix.build.packages {
        inherit python;
      })
          .overrideScope
      (
        lib.composeManyExtensions [
          inputs.pyproject-build-systems.overlays.default
          overlay
          sdistBuildDeps
        ]
      );

    env = pythonSet.mkVirtualEnv "caliptra-reg-gen" workspace.deps.default;
  in
    env;
in
  mkEnv python313
