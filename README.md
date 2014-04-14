A safe version of robinhood hashing. This code is based on the
existing Robinhood hasing algorithm, but rewritten to have a safer,
core interface that makes better use of static guarantees and requires
fewer dynamic checks.


## Benchmarks

On my machine, the standard rustc hashmap yields:

```
test hashmap::bench::find_existing                ... bench:        71 ns/iter (+/- 5)
test hashmap::bench::find_nonexisting             ... bench:        64 ns/iter (+/- 13)
test hashmap::bench::find_pop_insert              ... bench:       341 ns/iter (+/- 10)
test hashmap::bench::hashmap_as_queue             ... bench:       189 ns/iter (+/- 2)
test hashmap::bench::insert                       ... bench:       224 ns/iter (+/- 19)
```

My version yields:

```
test bench::find_existing    ... bench:        67 ns/iter (+/- 7)
test bench::find_nonexisting ... bench:        62 ns/iter (+/- 8)
test bench::find_pop_insert  ... bench:       350 ns/iter (+/- 11)
test bench::hashmap_as_queue ... bench:       208 ns/iter (+/- 3)
test bench::insert           ... bench:       227 ns/iter (+/- 8)
```

As you can see, the two are pretty close.
