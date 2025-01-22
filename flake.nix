{
  description = "tmbb";

  inputs = { nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable"; };

  outputs = { self, nixpkgs }: {
    packages = nixpkgs.lib.genAttrs [ "x86_64-linux" ] (system:
      let pkgs = import nixpkgs { inherit system; };
      in rec {
        tmbb = pkgs.stdenv.mkDerivation {
          pname = "tmbb";
          version = "0.0.0";

          src = ./.;

          buildInputs = [ pkgs.stdenv.cc pkgs.gmp ];

          buildPhase = ''
            make PREFIX=$out
          '';

          meta = with pkgs.lib; { description = "tmbb"; };
        };
      });

    defaultPackage = { x86_64-linux = self.packages.x86_64-linux.tmbb; };
  };
}
