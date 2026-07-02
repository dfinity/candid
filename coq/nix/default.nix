{}:
let
  subpath = import ./gitSource.nix;

  # Re-pinned to a modern nixpkgs that provides coq_8_18.
  #
  # The previous niv pin (nixos-20.09) no longer evaluates on current nix, and
  # the default `coq` is now Rocq 9.x, which renamed the stdlib namespace
  # (Coq.* -> Stdlib.*) and relocated FunInd — both of which these proofs use.
  # coq_8_18 is the newest coq that still accepts them unchanged.
  nixpkgs = fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/e8273b29fe1390ec8d4603f2477357555291432e.tar.gz";
    sha256 = "sha256-mFP086y1bNA1g9AsY/pCue3H3W2R7ayroHyRbZrcMf0=";
  };

  overlays = [
    (pkgs: super: { local = {
      # the main product: building the theories
      theories = pkgs.stdenv.mkDerivation {
        name = "candid-coq";
        src = subpath ./..;
        buildInputs = [
          pkgs.dune_2
          pkgs.coq_8_18
          pkgs.coq_8_18.ocaml
          pkgs.coq_8_18.ocamlPackages.findlib
        ];
        buildPhase = ''
          dune build --display=short
        '';
        installPhase = ''
          touch $out
        '';
      };

      # a convenient shell setup
      shell = pkgs.mkShell {
        inputsFrom = [
          pkgs.local.theories
        ];
      };
    };})
  ];

in import nixpkgs { inherit overlays; }
