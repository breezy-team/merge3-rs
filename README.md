Merge3
======

A rust implementation of 3-way merge of texts.

Given BASE, OTHER, THIS, tries to produce a combined text
incorporating the changes from both BASE->OTHER and BASE->THIS.
All three will typically be sequences of lines.

The implementation is primarily meant to be used with text files, but
it should work with any type that can be represented as a sequence of
lines.

Usage
=====

From the command-line::

```shell

$ echo foo > mine
$ echo bar > base
$ echo blah > other
$ merge3 mine base other > merged
$ cat merged
```

Or from rust:

```rust

use merge3::Merge3;

fn main() {
    let base = vec!["common\n", "base\n"];
    let this = vec!["common\n", "a\n"];
    let other = vec!["common\n", "b\n"];

    let m3 = Merge3::new(&base, &this, &other);

    for line in m3.merge_lines() {
        println!("{}", line);
    }
}
```
