virtualenv --python=python3 venv
source venv/bin/activate
pip install -r compileUtils/requirements.txt
rm -rf customlib
find . -iname '*.ml' -or -iname '*.mli' | grep -v '_esy\|_build' | esy depgraph > depend.dot
mkdir customlib
cp compileUtils/dune_for_compcert customlib/dune
cp compcert.ini customlib/compcert.ini
python compileUtils/makeCopyScript.py
sh moveScript.sh