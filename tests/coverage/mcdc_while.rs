#![feature(coverage_attribute)]
//@ edition: 2021
//@ min-llvm-version: 18
//@ compile-flags: -Zcoverage-options=mcdc
//@ llvm-cov-flags: --show-mcdc

fn mcdc_while_33_percent() {
    let values = [(false, true, true), (true, false, true), (true, false, false)];
    let mut i = 0;

    while (values[i].0 && values[i].1) || values[i].2 {
        i += 1
    }
}

fn mcdc_while_66_percent() {
    let values =
        [(false, true, true), (true, false, true), (true, true, true), (false, false, false)];
    let mut i = 0;

    while (values[i].0 && values[i].1) || values[i].2 {
        i += 1
    }
}

fn mcdc_while_100_percent(values: &[(bool, bool, bool)]) {
    let mut i = 0;

    while (values[i].0 && values[i].1) || values[i].2 {
        i += 1
    }
}

#[coverage(off)]
fn main() {
    mcdc_while_33_percent();

    mcdc_while_66_percent();

    let values_1 = [(true, true, true), (true, false, false)];
    let values_2 = [(false, true, true), (false, false, false)];
    mcdc_while_100_percent(&values_1);
    mcdc_while_100_percent(&values_2);
}
