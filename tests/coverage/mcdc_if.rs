#![feature(coverage_attribute)]
//@ edition: 2021
//@ compile-flags: -Zcoverage-options=mcdc
//@ llvm-cov-flags: --show-mcdc

fn mcdc_check_neither(a: bool, b: bool) {
    if a && b {
        say("a and b");
    } else {
        say("not both");
    }
}

fn mcdc_check_a(a: bool, b: bool) {
    if a && b {
        say("a and b");
    } else {
        say("not both");
    }
}

fn mcdc_check_b(a: bool, b: bool) {
    if a && b {
        say("a and b");
    } else {
        say("not both");
    }
}

fn mcdc_check_both(a: bool, b: bool) {
    if a && b {
        say("a and b");
    } else {
        say("not both");
    }
}

fn mcdc_check_tree_decision(a: bool, b: bool, c: bool) {
    // This expression is intentionally written in a way
    // where 100% branch coverage indicates 100% mcdc coverage.
    if a && (b || c) {
        say("pass");
    } else {
        say("reject");
    }
}

fn mcdc_check_not_tree_decision(a: bool, b: bool, c: bool) {
    // Contradict to `mcdc_check_tree_decision`,
    // 100% branch coverage of this expression does not mean indicates 100% mcdc coverage.
    if (a || b) && c {
        say("pass");
    } else {
        say("reject");
    }
}

#[coverage(off)]
fn main() {
    mcdc_check_neither(false, false);
    mcdc_check_neither(false, true);

    mcdc_check_a(true, true);
    mcdc_check_a(false, true);

    mcdc_check_b(true, true);
    mcdc_check_b(true, false);

    mcdc_check_both(false, true);
    mcdc_check_both(true, true);
    mcdc_check_both(true, false);

    mcdc_check_tree_decision(false, true, true);
    mcdc_check_tree_decision(true, true, false);
    mcdc_check_tree_decision(true, false, false);
    mcdc_check_tree_decision(true, false, true);

    mcdc_check_not_tree_decision(false, true, true);
    mcdc_check_not_tree_decision(true, true, false);
    mcdc_check_not_tree_decision(true, false, false);
    mcdc_check_not_tree_decision(true, false, true);
}

#[coverage(off)]
fn say(message: &str) {
    core::hint::black_box(message);
}
