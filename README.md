# XSmallTest

## Introduction ##

XSmallTest (XSM) is a minimal single-header implementation of a test DSL that
generates test cases compatible with Xcode's XCTest.

## Usage ##

Simply include XSmallTest.h, declare your test case with `xsm_given`, and
write test sections with arbitrarily nested `xsm_when` and `xsm_then` statements:

    #import "XSmallTest.h"

    xsm_given("an integer value") {
        int v;
        xsm_when("the value is 42") {
            v = 42;

            xsm_then("the value is the answer to the life, the universe, and everything") {
                XCTAssertEqual(42, v);
            }
        }
    }

Set-up and tear-down can be performed inline, based on standard C/Objective-C nesting rules; XSM conditionalizes
execution of the test blocks automatically based on nesting.

Standard XCTest assertions are supported, as are Xcode 6's asynchronous testing APIs. Within the context of a test section,
`self` refers to a valid XCTestCase instance.

### TODO ###

- Performance testing (Xcode 6). This will likely require exposing a new clause (`measure()`) that generates XCTest
  selectors ending with 'Performance'.