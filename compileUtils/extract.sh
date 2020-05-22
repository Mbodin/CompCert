rm -rf customlib
make clean
rm -rf venv
esy ./configure x86_64-macosx
esy make -j 4
sh compileUtils/moveFiles.sh
