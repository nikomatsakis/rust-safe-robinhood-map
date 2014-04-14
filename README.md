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

but my version yields:

```
test bench::find_existing    ... bench:        68 ns/iter (+/- 5)
test bench::find_nonexisting ... bench:        63 ns/iter (+/- 11)
test bench::find_pop_insert  ... bench:       355 ns/iter (+/- 7)
test bench::hashmap_as_queue ... bench:       210 ns/iter (+/- 4)
test bench::insert           ... bench:       238 ns/iter (+/- 10)
```
