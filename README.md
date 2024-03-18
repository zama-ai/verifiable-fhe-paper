# Verifiable PBS

This project allows to prove an execution of TFHE's PBS using [plonky2](https://github.com/0xPolygonZero/plonky2). For details, see the [paper](https://eprint.iacr.org/2024/451). 

## Parameters
Most parameters are set in `src/main.rs`, the notable exception being the ring dimension `N`. The latter is set in `src/ntt/mod.rs` by pointing the `param` module to the corresponding `param_{N}.rs` file. We suggest to use `N=8` for testing and `N=1024` to run the `main` file. NTT parameter files are available for other values of `N`, and the folder also contains [Sage](https://www.sagemath.org/) code to generate more. However, choosing another value of `N` might require to set a technical circuit parameter as outlined in [this comment](https://github.com/zama-ai/vPBS/blob/10a7931ae5d5d7f48611557e056fb933d1ec7398/src/vtfhe/ivc_based_vpbs.rs#L54).

## Run
To run the tests, simply use
```
    cargo test --release
```
As mentioned above, we recommend using `N=8` for this. Large values of `N` will result in a stack overflow error. Note that there is one test, namly `vtfhe::tests::test_blind_rot`, which is flaky because the parameters are not large enough to always account for the rounding error introduced by the mod switch. 

To reproduce the results from the paper, simply run
```
    cargo run --release
```
with `N=1024`.

## Disclaimer
This implementation is purely for academic purposes and not meant for production.

## License
Following plonky2, the code in this repository is licensed under either of
- Apache License, Version 2.0
- MIT license

at your option.
