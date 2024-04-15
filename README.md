Merge3
======

A rust implementation of 3-way merge of texts.

Given BASE, OTHER, THIS, tries to produce a combined text
incorporating the changes from both BASE->OTHER and BASE->THIS.
All three will typically be sequences of lines.

Usage
=====

From the command-line::

    $ echo foo > mine
    $ echo bar > base
    $ echo blah > other
    $ merge3 mine base other > merged
    $ cat merged

Or from rust:

```rust

use merge3::Merge3;

fn main() {
    let base = vec!["common".to_string(), "base".to_string()];
    let this = vec!["common".to_string(), "a".to_string()];
    let other = vec!["common".to_string(), "b".to_string()];

    let m3 = Merge3::new(&base, &this, &other);

    for line in m3.merge_annotated() {
        println!("{}", line);
    }
}
```
