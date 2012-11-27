## aplcompile: An APL Compiler in Standard ML

This software implements an APL compiler in Standard ML. 

See [the compilation scheme](aplcompile/comp.md).

## Try it!

The software makes use of the [smlunicode
library](https://github.com/melsman/smlunicode) project for lexing and
the [aplparse](https://github.com/melsman/aplparse) project for
parsing, which means that you need to checkout the
[smlunicode](https://github.com/melsman/smlunicode) sources and the
[aplparse](https://github.com/melsman/aplparse) sources in folders
next to the `aplcompile` sources.

You also need a Standard ML compiler (e.g., [Mlton](http://www.mlton.org/)).

Then simply write `make test` followed by `./test` in your shell.

## Limitations

Todo: Operators and improved error handling.

## License

This software is published under the [MIT License](MIT_LICENSE.md).

