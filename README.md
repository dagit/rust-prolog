# Overview
Rust implementation of prolog based on miniprolog: http://andrej.com/plzoo/html/miniprolog.html

I translated miniprolog from the above SML sources to Rust for two primary reasons:

  * Firstly, I wanted a project to explore programming in Rust
  * Secondly, prolog is interesting but I never felt like I properly learned it

Starting from an existing implementation was nice because it shortened the time to a working
version. The current version in this repository is very much a work in progress and overly simplistic.
I plan to improve it to better learn Rust and I plan to improve it as I learn Rust :)

In other words, this is really a playground for me to play with both Rust and prolog.

# Installation

Tested on Linux (Fedora 22), OSX, and Windows. You will need to install readline.

## Windows
On Windows the easiest way to install readline is by using [msys2's pacman](https://msys2.github.io/)
and then configuring Cargo to so that it can find the dll. I have the following in
`C:\Users\<username>\.cargo\config`:

```
[target.x86_64-pc-windows-gnu.readline]
rustc-link-search = ["C:/msys64/mingw64/bin"]
rustc-link-lib = ["readline6"]
root = "C:/msys64/mingw64/bin"
```

## OSX

I use homebrew to install readline.

## Linux

Make sure you have the development package for readline. In Fedora this is `readline-devel`.
In Debian/Ubuntu based distributions it is likely named `readline-dev`.

# Example

```
$ cargo run
Welcome to miniprolog!
This prolog interpreter is based on the ML code at the PLZoo:
  http://andrej.com/plzoo/html/miniprolog.html

Input syntax: 
    ?- query.            Make a query.
    a(t1, ..., tn).      Assert an atomic proposition.
    A :- B1, ..., Bn.    Assert an inference rule.
    $quit                Exit interpreter.
    $use "filename"      Execute commands from a file.
Prolog> $use "likes.pl"
Prolog> ?- likes(X,Y).
Y = mary
X = john 

more? (y/n) [y] 
```

# Roadmap

I haven't figured out exactly which directions I want to take this in, but some
ideas I've been kicking around include:

  * Compile to the [Warren Abstract Machine](http://wambook.sourceforge.net/)
  * Add a [type system](http://www.cs.bham.ac.uk/~udr/papers/TypedProlog.pdf)
  * Change the search procedure to a [complete search](http://www.ai.sri.com/~stickel/pttp.html).
  * Add more primitive types, lists, numbers, etc and make a small standard library.
