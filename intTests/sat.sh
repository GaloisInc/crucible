# Shell functions for testing SAT and UNSAT.
#
# Uses environment variables exported by './runtests.sh'; to use, add
# '. ../sat.sh' into './<test>/test.sh' script.

# The return values below -- 10 for SAT and 20 for UNSAT -- were
# determined empirically. I couldn't find anything in the sat4j docs
# about this.

# Convert Windows EOLs to Unix EOLs.
#
# On Windows SAW (via ABC?) produces Windows EOLs in .cnf files, but
# sat4j requires Unix EOLs. This is a no-op on Unix for text files.
_dos2unix () {
    sed -i -e 's/\r\n/\n/' "$1"
}

# Run sat4j, jumping through appropriate hoops on Windows.
_sat4j () {
    SAT4J_JAR=$TESTBASE/jars/org.sat4j.core.jar
    if [ "$OS" == "Windows_NT" ]; then
        _dos2unix "$1"
        # The .jar path must be a Windows-style path on Windows.
        SAT4J_JAR="$(cygpath -w "$SAT4J_JAR")"
    fi
    java -jar $SAT4J_JAR "$1"
}

# Succeed iff input DIMACS CNF file is satisfiable.
sat () {
(
    set +e
    _sat4j "$1"
    [ $? -eq 10 ] || exit 1
)
}

# Succeed iff input DIMACS CNF file is unsatisfiable.
unsat () {
(
    set +e
    _sat4j "$1"
    [ $? -eq 20 ] || exit 1
)
}
