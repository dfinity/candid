{}:
let
  sources =  import ./sources.nix;

  subpath = import ./gitSource.nix;

  overlays = [
    (pkgs: super: { local = {
      # Fetch niv from nix/sources.json, newer than nixpkgs
      niv = (import sources.niv {}).niv;

      # the main product: building the theories
      theories = pkgs.stdenv.mkDerivation {
        name = "candid-coq";
        src = subpath ./..;
        buildInputs = [
          pkgs.dune_2
          pkgs.coq
          pkgs.ocaml
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
        propagatedBuildInputs = [
          pkgs.niv
        ];

        # This helps with using GUI programs like coqide
        LOCALE_ARCHIVE = pkgs.stdenv.lib.optionalString pkgs.stdenv.isLinux "${pkgs.glibcLocales}/lib/locale/locale-archive";

        # allow building this as a derivation, so that CI can biuld and cache
        # the dependencies of shell
        phases = ["installPhase" "fixupPhase"];
        installPhase = ''
          mkdir $out
        '';
        preferLocalBuild = true;
        allowSubstitutes = true;
      };
    };})
  ];

in import sources.nixpkgs { inherit overlays; }

