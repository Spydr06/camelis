# camelis - A Lisp-like programming language written in OCaml

This is a little project to get me familiar with OCaml and functional programming in general.

**Main reference:**
[https://bernsteinbear.com/blog/lisp](https://bernsteinbear.com/blog/lisp)

### Usage

After downloading the repository, compile `camelis`:

```console
$ chmod +x ./build.sh
$ ./build.sh
```

Without `build.sh` script:

```console
$ ocamlc std.ml camelis.ml -o camelis
```

Running examples:

```console
$ ./camelis examples/helloworld.l
```

Repl:

```console
$ ./camelis
> ; enter code here
```

### License

This code is licensed under the [MIT License](https://mit-license.org). See [LICENSE](./LICENSE) for more information.
