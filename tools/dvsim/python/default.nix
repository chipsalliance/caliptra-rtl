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

    pythonSet =
      (pkgs.callPackage inputs.pyproject-nix.build.packages {
        inherit python;
      })
          .overrideScope
      (
        lib.composeManyExtensions [
          inputs.pyproject-build-systems.overlays.default
          overlay
          # Wheel-first (see sourcePreference above): only first-party
          # source-only deps need an override. compile-to-core has no wheel, so
          # it builds from sdist and must declare its PEP 517 backend.
          (final: prev: {
            compile-to-core = prev.compile-to-core.overrideAttrs (old: {
              nativeBuildInputs = old.nativeBuildInputs ++ (final.resolveBuildSystem {hatchling = [];});
            });
          })
        ]
      );

    env = pythonSet.mkVirtualEnv "caliptra-dvsim" workspace.deps.default;
  in
    env;
in
  mkEnv python313
