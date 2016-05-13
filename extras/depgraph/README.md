Generating Dependency Graph
============================

Usage:

    ./leandeps.py [options] dir/file

For example:

    ./leandeps.py ../../library/

If argument is a directory, all source files below that directory will be included in the graph.

 - `-h`/`--help` : prints this message
 - `-o <file>`/`--output <file>` : saves the DOT output in the specified file

If no output file is specified, `deps.gv` and `deps.gv.dot` is written to.

You need [graphviz][graphviz] and the [graphviz python library][python-graphviz]. If you already have [pip][pip], you can do:

    sudo apt-get install graphviz
    sudo pip install graphviz

The resulting `deps.gv.dot` file can be run through tred and [dot][graphviz] from graphviz to produce,
e.g., an svg file. For example:

    tred deps.gv.dot > treddeps.dot
    dot -Tsvg -O treddeps.dot

[python-graphviz]: https://pypi.python.org/pypi/graphviz
[graphviz]: http://www.graphviz.org/
[pip]: https://pip.readthedocs.org/en/stable/installing/#install-pip
