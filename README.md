# Diqt

Coq hash table library

## Overview of the development

* [`src`](./src/) - Source code for hash tables
    * [`src/Table.v`](./src/Table.v) - Hashtable with PArray
    * [`src/Radix.v`](./src/Radix.v) - Hashtable with Radix tree
    * [`src/Keys.v`](./src/Keys.v) - Module HashI/HashP for Hashtable functor
    * [`src/Hashtable.v`](./src/HashTable.v) - Glue code for Hashtable with
      int keys
    * [`src/HashtablePositive.v`](./src/HashTablePositive.v) - Glue code for
      Hashtable with Positive keys
    * [`src/Int_utils.v`](./src/Int_utils.v) - Lemma and function on int
      like `fold_int`
* [`tests`](./tests/) - Test code
    * [`tests/fibo.v`](./tests/fibo.v) - Hashtable int test on Fibonacci function
    * [`test/pascal.v`](./tests/pascal.v) - HashTable int test on Pascal function
    * [`test/pascal_pos.v`](./tests/pascal_pos.v) - HashTable positive test on
      Pascal function
    * [`test/syracuse.v`](./tests/syracuse.v) - HashTable int test on Syracuse
      function
    * [`test/syracuse_pos.v`](./tests/syracuse_pos.v) - HashTable positive test on
      Syracuse verification  function
