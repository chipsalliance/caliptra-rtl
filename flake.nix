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
  description = "caliptra-rtl Nix Packages and Environments";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    flake-utils.url = "github:numtide/flake-utils";

    ##########
    # PYTHON #
    ##########

    pyproject-nix = {
      url = "github:pyproject-nix/pyproject.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    pyproject-build-systems = {
      url = "github:pyproject-nix/build-system-pkgs";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.pyproject-nix.follows = "pyproject-nix";
      inputs.uv2nix.follows = "uv2nix";
    };
    uv2nix = {
      url = "github:pyproject-nix/uv2nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.pyproject-nix.follows = "pyproject-nix";
    };
  };

  outputs = inputs: let
    all_system_outputs = inputs.flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import inputs.nixpkgs {
        inherit system;
      };
      python_dvsim = pkgs.callPackage ./tools/dvsim/python {inherit inputs;};

      # Environment variables derivable from the repo layout.
      # Variables that cannot be auto-set here:
      #   CALIPTRA_WORKSPACE — user-specific parent dir for verilator scratch output
      #   RV_ROOT            — external VeeR-EL2 checkout (not a submodule)
      commonShellHook = ''
        export CALIPTRA_ROOT="$(git rev-parse --show-toplevel)"
        export ADAMSBRIDGE_ROOT="$CALIPTRA_ROOT/submodules/adams-bridge"
      '';
    in {
      devShells = rec {
        default = caliptra-dvsim;
        caliptra-dvsim = pkgs.mkShell {
          name = "caliptra-dvsim";
          packages = ([
            python_dvsim
          ]) ++ (with pkgs; [
            uv
          ]);
          shellHook = commonShellHook;
        };
      };
    });
  in
    all_system_outputs;
}
