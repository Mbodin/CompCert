## Comparison with Absint/CompCert

This file contains an explaination of what this different between this fork of CompCert and the original Abstin/CompCert repository.

- Defines a PrintCSharpMinor.ml file to print the C#m AST.
- Adds a custom script that builds + extract Compcert using the existing Makefile,
  choses the right set of submodules that I need and copies the associated ocaml files in a separate folder,
  along with the Dune file to build them. (see compileUtils folder)
- modifies the `configure` file to allow for ingoring if Coq is not installed
  (it is not called when compiling the custom library).
- modifies the `Makefile` to allow for creation of the 'compcert.ini' file only.
- Adds a snapshot of the extracted files according to the custom build script in `customlib/`
- Adds a package.json file + esy.lock to easily package the lib with esy.
