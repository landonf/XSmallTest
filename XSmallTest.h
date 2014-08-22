/*
 * Copyright (c) 2014 Landon Fuller <landon@landonf.org>
 * All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

#import <XCTest/XCTest.h>

#import <inttypes.h>

#import <objc/runtime.h>
#import <objc/message.h>

#import <mach-o/getsect.h>
#import <dlfcn.h>

/*
 * The pseudo root section tag; references the last previously declared section; any section referencing this
 * parent is either 1) a root XSM_SECTION_TYPE_TEST_CASE, or 2) a XSM_SECTION_TYPE_NESTED that should be connected
 * with a previously declared XSM_SECTION_TYPE_TEST_CASE.
 *
 * This tag is reserved via the XSM_TEST_PARENT_RESERVED_ definition below.
 */
#define INT_XSM_ORPHAN_TAG 0

/* The pseudo root section tag; references the last previously declared section. Since __COUNTER__ is gauranteed to start
 * at 0 and increment monotonically, we declare this field first to ensure that no other __COUNTER__-derived tag value
 * will be 0. */
static const int XSM_TEST_PARENT_TAG __attribute__((used)) = INT_XSM_ORPHAN_TAG;

/* Ensures that XSM_TEST_PARENT_TAG's '0' value is reserved by allocating it (or a greater value). If __COUNTER__ is already greater than 0,
 * our gaurantees still hold. */
static const int XSM_TEST_PARENT_RESERVED_ __attribute__((unused)) = __COUNTER__;

/**
 * Define a new test case with the given description. All tests must first be defined via xsm_given().
 *
 * Example:
 @code
 xsm_given("an integer value") {
    // Assertions or additional sections
 }
 @endcode
 *
 * @param desc The clause's description.
 */
#define xsm_given(description) int_xsm_given_(description, __COUNTER__) // indirection required to ensure __COUNTER__ is expanded
#define int_xsm_given_(description, tag) int_xsm_given__(description, tag)
#define int_xsm_given__(__xsm_description, __xsm_tag) \
    /* Declare our test case's method IMP */ \
    static void int_xsm_test_func_ ## __xsm_tag (XCTestCase *self, SEL _cmd, NSMutableSet *INT_XSM_TEST_TAGS); \
    \
    /* Record the section */ \
    int_xsm_write_section_record(XSM_SECTION_TYPE_TEST_CASE, XSM_CLAUSE_TYPE_GIVEN, __xsm_description, XSM_TEST_PARENT_TAG, __xsm_tag, &int_xsm_test_func_ ## __xsm_tag) \
    \
    /* Define a constructor to perform test case class registration */ \
    __attribute__((constructor)) static void int_xsm_parse_test_records_ ## __xst_case_name (void) { \
        int_xsm_parse_test_records(); \
    } \
    \
    /* Define the test case method IMP (sans body, which the user must provide. We provide 'self' and _cmd to support
    * Objective-C-based invocation from our custom XCTestCase */ \
    static void int_xsm_test_func_ ## __xsm_tag (XCTestCase *self, SEL _cmd, NSMutableSet *INT_XSM_TEST_TAGS)

/**
 * Define a new test `when' clause with the given description. All tests must first be defined via xsm_given().
 *
 * Example:
 @code
 xsm_given("an integer value") {
    int v;
    xsm_where("the value is 42") {
        v = 42;
        // Additional sections or tests here
    }
 }
 @endcode
 *
 * @param desc The clause's description.
 */
#define xsm_when(description) int_xsm_generic_sect(description, XSM_CLAUSE_TYPE_WHEN, XSM_TEST_PARENT_TAG, __COUNTER__)

/**
 * Define a new `then' clause with the given description. All tests must first be defined via xsm_given().
 *
 * Example:
 @code
 xsm_given("an integer value") {
    int v;
    xsm_when("the value is 42") {
        v = 42;
 
        xsm_then("the value is the answer to the life, the universe, and everything") {
            XCTAssertEqual(42, v);
        }
    }
 
    xsm_then("this test should fail") {
        XCTFail("ints are smelly");
    }
 }
 @endcode
 *
 * @param desc The clause's description.
 */
#define xsm_then(description) int_xsm_generic_sect(description, XSM_CLAUSE_TYPE_THEN, XSM_TEST_PARENT_TAG, __COUNTER__)

/* Generic nested section declaration */
#define int_xsm_generic_sect(description, clause_type, parent_tag, tag) int_xsm_generic_sect_(description, clause_type, parent_tag, tag) // indirection required to ensure __COUNTER__ is expanded
#define int_xsm_generic_sect_(__xsm_description, __xsm_clause_type, __xsm_parent_tag, __xsm_tag) \
    /* Record the section */ \
    int_xsm_write_section_record(XSM_SECTION_TYPE_NESTED, __xsm_clause_type, __xsm_description, __xsm_parent_tag, __xsm_tag, NULL /* always NULL for our sub-sections */) \
    \
    /* Create a new XSM_TEST_PARENT_TAG for this scope and check the scope against INT_XSM_TEST_TAGS */ \
    for (const int XSM_TEST_PARENT_TAG = __xsm_tag; int_xsm_sect_tag_check(INT_XSM_TEST_TAGS, __xsm_tag, XSM_TEST_PARENT_TAG);)

/**
 * @internal
 * Record a test case section with the given section type, clause type, description, and file-scoped order.
 *
 * @param __xsm_type The section type (xsm_section_type_t) to declare.
 * @param __xsm_clause The clause type (xsm_clause_type_t) to declare.
 * @param __xsm_description The section's description, as a constant string.
 * @param __xsm_parent_tag The section's parent's order tag, or 0 if this is a top-level or second-level section (in which case, parentage has to be
 * reconstructed from the order tags)
 * @param __xsm_tag The section's translation-unit-scoped order tag.
 * @param __xsm_sect_func The section's implementation function (int_xsm_test_section_function_t).
 */
#define int_xsm_write_section_record(__xsm_type, __xsm_clause, __xsm_description, __xsm_parent_tag, __xsm_tag, __xsm_sect_func) \
    /* Try to provide a decent error message if a non-constant description is provided */ \
    __attribute__((unused)) static char xsm_description_messages_must_be_constant_strings_ ## __xsm_tag[__builtin_constant_p(__xsm_description) ? 1 : -1]; \
    \
    INT_XSM_MAKE_SECT_RECORD(__xsm_type, __xsm_clause, __xsm_description, __xsm_parent_tag, __xsm_tag, __xsm_sect_func)

/* Write a section record to __DATA,xsm_tests */
#define INT_XSM_MAKE_SECT_RECORD(__xsm_type, __xsm_clause, __xsm_description, __xsm_parent_tag, __xsm_tag, __xsm_sect_func) \
struct int_xsm_sect_record_record_ ## __xsm_tag ## _t { \
    int_xsm_section_record record; \
    char description[sizeof(__xsm_description)]; \
} __attribute__((packed)); \
\
static struct int_xsm_sect_record_record_ ## __xsm_tag ## _t int_xsm_sect_record_record_ ## __xsm_tag __attribute__((section(XSM_SEG_NAME "," XSM_SECT_NAME))) __attribute__((used)) = { \
    .record = { \
        .size = sizeof(struct int_xsm_sect_record_record_ ## __xsm_tag ## _t), \
        .version = 0, \
        .type = (uint8_t) __xsm_type, \
        .clause = (uint8_t) __xsm_clause, \
        .tu = &int_xsm_local_translation_unit, \
        .parent_tag = __xsm_parent_tag, \
        .tag = __xsm_tag, \
        .description = (char *) 0 /* description directly follows */, \
        .section_class = nil, \
        .section_imp = __xsm_sect_func \
    }, \
    .description = __xsm_description \
};

/**
 * The segment to which XSM's section records are written
 */
#define XSM_SEG_NAME "__DATA"

/** 
 * The section (within XSM_SEG_NAME) to which XSM's section records are written
 */
#define XSM_SECT_NAME "xsm_tests"

/**
 * The section (within XSM_SEG_NAME) to which XSM's translation unit records are written.
 */
#define XSM_TU_SECT_NAME "xsm_txu"


/* Internal ARC compatibility macros */
#if __has_feature(objc_arc)
#   define INT_XSM_RETAIN(obj)
#   define INT_XSM_RELEASE(__xsmall_obj) __xsmall_obj = nil;
#   define INT_XSM_MRC_ONLY(expr)
#else
#   define INT_XSM_RETAIN(__xsmall_obj) [__xsmall_obj retain];
#   define INT_XSM_RELEASE(__xsmall_obj) ([__xsmall_obj release] && __xsmall_obj = nil);
#   define INT_XSM_MRC_ONLY(expr) expr
#endif

/**
 * XSM Clause Types
 */
typedef NS_ENUM(uint16_t, xsm_clause_type_t) {
    /** A top-level test case. In the BDD unit test style, this would be equivalent to a 'Given' declaration. */
    XSM_CLAUSE_TYPE_GIVEN = 0,

    /** An inner 'when' test clause. */
    XSM_CLAUSE_TYPE_WHEN = 1,

    /** An inner 'then' test clause. */
    XSM_CLAUSE_TYPE_THEN = 2,
};

/**
 * XSM Hierarchical Section Types
 */
typedef NS_ENUM(uint16_t, xsm_section_type_t) {
    /** A top-level test case. */
    XSM_SECTION_TYPE_TEST_CASE = 0,
    
    /** An inner (nested) section. */
    XSM_SECTION_TYPE_NESTED = 1
};

/*
 * XSM translation unit record.
 */
typedef struct int_xsm_translation_unit {
    /**
     * Record version. The current version is 0; if an incompatible change is made to this data format, this value should be incremented.
     */
    uint16_t version;
} int_xsm_translation_unit;

/*
 * A test section implementation.
 *
 * @param self An XCTestCase instance.
 * @param _cmd The selector allocated for this test function.
 * @param tags The section tags enabled for this test run.
 */
typedef void (int_xsm_test_section_function_t)(XCTestCase *self, SEL _cmd, NSMutableSet *tags);

/*
 * XSM test record. Test records are written to the __DATA,xsm_tests section when declared via the
 * XSM test macros.
 */
typedef struct int_xsm_section_record {
    /** Size of this record (including the size field). */
    uint16_t size;
    
    /**
     * Record version. The current version is 0; if an incompatible change is made to this data format, this value
     * should be incremented. To avoid incompatibilities, -always- add additional fields to the -end- of this
     * structure.
     */
    uint16_t version;
    
    /** The type of this section (xsm_section_type_t). */
    uint16_t type;
    
    /** The clause to use when presenting this test section (xsm_clause_type_t). */
    uint16_t clause;
    
    /** The section's description. When serialized, this will be the offset from the end of this structure element. */
    char *description;
    
    /** A symbol-based reference to the containing translation unit */
    int_xsm_translation_unit *tu;
    
    /** The section parent's order tag. For top-level and second-level sections, this will be 0 due to implementation
     * constraints; the actual parent reference must be reconstructed by ordering all the parsed sections within
     * a translation unit, and inserting orphaned sections into the previously parsed XSM_SECTION_TYPE_TEST_CASE test
     * case. */
    uint32_t parent_tag;
    
    /** The section's order tag. This can be used to reconstruct the in-source ordering of sections within
     * a single file */
    uint32_t tag;
    
    /** The runtime-created test case class for this test section. This is initialized at runtime */
    Class section_class;

    /** The method IMP for this test section, or NULL if the parent's test function should be used. */
    int_xsm_test_section_function_t *section_imp;
} int_xsm_section_record;

/*
 * A common translation unit record, used by all test sections defined within
 * the current translation unit
 */
static int_xsm_translation_unit int_xsm_local_translation_unit __attribute__((section(XSM_SEG_NAME "," XSM_TU_SECT_NAME))) = {
    .version = 0
};

/* Function foward-declarations */
static inline BOOL int_xsm_sect_tag_check (NSMutableSet *tags, int expected, int parent);
static inline id int_xsm_meth_impl_cls_defaultTestSuite (id self, SEL _cmd);
static inline int_xsm_test_section_function_t *int_xsm_meth_impl_testEntry (XCTestCase *self, SEL _cmd);
static inline void int_xsm_meth_impl_xsmTestSection (XCTestCase *self, SEL _cmd);
static inline id int_xsm_meth_impl_name (XCTestCase *self, SEL _cmd);

static inline SEL int_xsm_register_test_selector (Class cls, const char *description, void (*imp)(XCTestCase *self, SEL _cmd));
static inline Class int_xsm_register_test_case_class (const char *description);

/*
 * Implements runtime parsing and registration of XSM test cases.
 */
static inline void int_xsm_parse_test_records (void) {
    /* Find the __DATA,xsm_tests section; this contains our registered test cases and sections. */
    struct {
        void *data;
        const void *end;
        unsigned long size;
    } xsm_sect;
    {
        /* Fetch the mach header */
        Dl_info dli;
        if (dladdr((const void *) &int_xsm_parse_test_records, &dli) == 0) {
            [NSException raise: NSInternalInconsistencyException format: @"Could not find our own image!"];
        }
        
        /* Fetch the section data */
#ifdef __LP64__
        xsm_sect.data = getsectiondata((const struct mach_header_64 *) dli.dli_fbase, XSM_SEG_NAME, XSM_SECT_NAME, &xsm_sect.size);
#else
        xsm_sect.data = getsectiondata((const struct mach_header_32 *) dli.dli_fbase, XSM_SEG_NAME, XSM_SECT_NAME, &xsm_sect.size);
#endif
        
        /* This should never happen; our constructor is only called if at least a test case has been registered */
        if (xsm_sect.data == NULL) {
            [NSException raise: NSInternalInconsistencyException format: @"Could not find __DATA,xsm_tests in %s", dli.dli_fname];
            __builtin_trap();
        }
        
        xsm_sect.end = (void *) ((uintptr_t)xsm_sect.data + xsm_sect.size);
    }
    
    /* Extract all registered tests */
    @autoreleasepool {
        void *ptr = xsm_sect.data;

        /* Parse all records for this translation unit */
        NSMutableArray *tagOrder = [NSMutableArray array]; /* tags */
        NSMutableDictionary *records = [NSMutableDictionary dictionary]; /* tag -> NSValue -> int_xsm_section_record ptr; */
        while (ptr != xsm_sect.end) {
            assert(ptr < xsm_sect.end);

            /* Save the record reference and advance ptr */
            int_xsm_section_record *rec = (int_xsm_section_record *) ptr;
            ptr = (void *) ((uint8_t *)ptr + rec->size);
            
            /* Skip invalid versions */
            if (rec->version != 0) {
                NSLog(@"Skipping invlid XSM test record version (%hu)", rec->version);
                continue;
            }
            
            /* If the node isn't within our translation unit, punt */
            if (rec->tu != &int_xsm_local_translation_unit)
                continue;
            
            /* Skip records that have already been registered */
            if (rec->section_class != nil)
                continue;

            /* Adjust relative data pointers */
            rec->description = (char *) ((uint8_t *) rec) + sizeof(*rec);
            
            /* Save the record */
            [tagOrder addObject: @(rec->tag)];
            records[@(rec->tag)] = [NSValue valueWithPointer: rec];

#ifdef INT_XSM_DEBUG
            NSLog(@"Found record %p (size=%hu, version=%hu) with type=%hu, clause=%hu, order=%u, desc=%s, parent=%u, imp=%p",
                  rec, rec->size, rec->version, rec->type, rec->clause, rec->tag, rec->description, rec->parent_tag, rec->section_imp);
#endif
        }
        
        /* Re-order the section's according to their tag order; this corresponds to the order they were declared
         * in this translation unit. */
        [tagOrder sortUsingComparator: ^NSComparisonResult(id obj1, id obj2) {
            return [(NSNumber *)obj1 compare: obj2];
        }];
        
        /* Fix up any parent references to the pseudo-test case tag (0). These are references to the most recently
         * defined test case. */
        {
            int_xsm_section_record *currentRoot = NULL;
            for (NSNumber *tag in tagOrder) {
                int_xsm_section_record *rec = (int_xsm_section_record *) [(NSValue *) records[tag] pointerValue];
                
                /* Record new roots -- we leave their parent_tag set to INT_XSM_ORPHAN_TAG */
                if (rec->type == XSM_SECTION_TYPE_TEST_CASE) {
                    assert(rec->parent_tag == INT_XSM_ORPHAN_TAG);
                    currentRoot = rec;
                    continue;
                }
                
                /* Skip non-orphan references */
                if (rec->parent_tag != INT_XSM_ORPHAN_TAG) {
                    continue;
                }

                /* There must already be a test case defined; the API makes anything else impossible */
                if (currentRoot == NULL)
                    [NSException raise: NSInternalInconsistencyException format: @"No parent test case was defined for section '%s'", rec->description];

                /* Fix up the ophan's parent tag reference. */
                rec->parent_tag = currentRoot->tag;
            }
        }
        
        /* Generate test cases for all tags */
        NSMutableDictionary *testCases = [NSMutableDictionary dictionary]; /* tag -> XCTestCase */
        NSMutableSet *allParentTags = [NSMutableSet set]; /* tag -- includes all test cases that have defined children */
        {
            NSMutableArray *tagStack = [NSMutableArray array];
            int_xsm_section_record *rootRecord = NULL;
            for (NSNumber *tag in tagOrder) {
                int_xsm_section_record *rec = (int_xsm_section_record *) [(NSValue *) records[tag] pointerValue];
                
                /* Adjust our parse state for the section type. */
                switch ((xsm_section_type_t) rec->type) {
                    case XSM_SECTION_TYPE_TEST_CASE:
                        /* This is a new root node; drop our previous tag stack, and set the new root node value */
                        [tagStack removeAllObjects];
                        rootRecord = rec;
                        break;
                        
                    case XSM_SECTION_TYPE_NESTED:
                        /* This is a child node; pop the stack until we hit this child's parent's tag. */
                        while ([tagStack count] > 0 && ![[tagStack lastObject] isEqual: @(rec->parent_tag)]) {
                            [tagStack removeLastObject];
                            assert([tagStack count] != 0);
                        }
                        break;
                }
                
                /* At this point, there *must* be a root record in well-formed data */
                assert(rootRecord != NULL);
                
                /* Register this section on the tag stack. */
                [tagStack addObject: @(rec->tag)];
                
                /* Register this sections' XCTestCase class, if necessary. */
                if (rec->section_class == nil) {
                    /* Nested sections get the root record's test case class -- which may also have to be registered on-demand. */
                    if (rootRecord->section_class == nil) {
                        rootRecord->section_class = int_xsm_register_test_case_class(rootRecord->description);
                    }
                    rec->section_class = rootRecord->section_class;
                }
                
                /* Register this sections' test IMP, if necessary. */
                if (rec->section_imp == NULL) {
                    assert(rootRecord->section_imp != NULL);
                    rec->section_imp = rootRecord->section_imp;
                }
                
                /* Format the section's description */
                NSString *description;
                switch ((xsm_clause_type_t) rec->clause) {
                    case XSM_CLAUSE_TYPE_GIVEN:
                        description = [NSString stringWithFormat: @"Given %s", rec->description];
                        break;
                    case XSM_CLAUSE_TYPE_WHEN:
                        description = [NSString stringWithFormat: @"when %s", rec->description];
                        break;
                    case XSM_CLAUSE_TYPE_THEN:
                        description = [NSString stringWithFormat: @"then %s", rec->description];
                        break;
                }
                
                /* Create a test case instance for this section */
                SEL testSel = int_xsm_register_test_selector(rec->section_class, rec->description, &int_xsm_meth_impl_xsmTestSection);
                XCTestCase *tc = [rec->section_class testCaseWithSelector: testSel];

                objc_setAssociatedObject(tc, (const void *) &int_xsm_meth_impl_name, description, OBJC_ASSOCIATION_RETAIN);
                objc_setAssociatedObject(tc, (const void *) &int_xsm_meth_impl_xsmTestSection, [NSSet setWithArray: tagStack], OBJC_ASSOCIATION_RETAIN);
                objc_setAssociatedObject(tc, (const void *) &int_xsm_meth_impl_testEntry, [NSValue valueWithPointer: (const void *) rec->section_imp], OBJC_ASSOCIATION_RETAIN);

                testCases[@(rec->tag)] = tc;
                
                /* Mark our parent as having a child */
                if (rec->parent_tag != INT_XSM_ORPHAN_TAG) {
                    [allParentTags addObject: @(rec->parent_tag)];
                }
            }
        }
        
        /* Export the parsed entries out to a test suite/test case instance tree. */
        {
            /* Convert all non-leaf nodes to test suites */
            for (NSNumber *tag in tagOrder) {
                if ([allParentTags containsObject: tag]) {
                    /* This is a non-leaf node; convert to a suite */
                    XCTestCase *tc = testCases[tag];
                    XCTestSuite *replacement = [XCTestSuite testSuiteWithName: tc.name];
                    testCases[tag] = replacement;
                }
            }
            
            /* Iterate over the test cases and combine them into test suite(s) */
            int_xsm_section_record *rootRecord = NULL;
            NSMutableArray *testCaseTags = [NSMutableArray array];
            XCTestSuite *rootSuite = nil;

            for (NSUInteger i = 0; i < tagOrder.count; i++) {
                NSNumber *tag = tagOrder[i];
                int_xsm_section_record *rec = (int_xsm_section_record *) [(NSValue *) records[tag] pointerValue];
                
                /* Root node, reset our state */
                if (rec->parent_tag == INT_XSM_ORPHAN_TAG) {
                    XCTest *test = testCases[@(rec->tag)];
                    rootRecord = rec;
                    rootSuite = [XCTestSuite testSuiteWithName: test.name];
                    [testCaseTags removeAllObjects];
                    
                    /* If the root node has children, its children should be directly attached to the containing test suite */
                    if ([allParentTags containsObject: @(rec->tag)])
                        testCases[@(rec->tag)] = rootSuite;
                } else {
                    assert(rootRecord != NULL);
                    assert(rootSuite != nil);
                }
                
                /* Include this tag in the output for the current root test case */
                [testCaseTags addObject: tag];
                
                /* If this is not the final entry in this test case, nothing left to do */
                if (i + 1 < tagOrder.count) {
                    NSNumber *nextTag = tagOrder[i + 1];
                    int_xsm_section_record *next = (int_xsm_section_record *) [(NSValue *) records[nextTag] pointerValue];
                    if (next->parent_tag != INT_XSM_ORPHAN_TAG)
                        continue;
                }

                /* We've iterated over the entire test case; nwo we can attach all children to their parent test suite. */
                for (NSNumber *tag in testCaseTags) {
                    int_xsm_section_record *rec = (int_xsm_section_record *) [(NSValue *) records[tag] pointerValue];

                    /* If this is the root node, we exclude it; it will either be included directly below if it's leaf node,
                     * or if it's not a leaf node, it simply provides an extraneous level of nesting below the root */
                    if (rec->tag == rootRecord->tag)
                        continue;
                    
                    XCTest *child = testCases[@(rec->tag)];
                    XCTestSuite *parent = testCases[@(rec->parent_tag)];
                    [parent addTest: child];
                }
                
                /* Attach the new test suite to the test case's class. */
                XCTest *defaultTestSuite;
                if (![allParentTags containsObject: @(rootRecord->tag)]) {
                    /* If the root node has no children, it should be used directly as the top-level suite */
                    defaultTestSuite = testCases[@(rootRecord->tag)];
                } else {
                    defaultTestSuite = rootSuite;
                }
                objc_setAssociatedObject(rootRecord->section_class, (const void *) &int_xsm_meth_impl_cls_defaultTestSuite, defaultTestSuite, OBJC_ASSOCIATION_RETAIN);

#ifdef INT_XSM_DEBUG
                NSLog(@"Registered test cases: %@", testCases);
#endif

                /* Clean up state */
                rootRecord = NULL;
                rootSuite = nil;
            }
        }
    }
}

/* Check whether our tag is enabled, and whether we've already been run. We don't actually need the parent tag here; this is just used
 * to quiesce unused variable warnings on the parent tag, and 'unused variable was used' warnings that trigger with __attribute__((unused)) */
static inline BOOL int_xsm_sect_tag_check (NSMutableSet *tags, int expected, int parent) {
    NSNumber *expectedObj = [NSNumber numberWithInt: expected];
    if (tags.count == 0 || ![tags containsObject: expectedObj])
        return NO;

    [tags removeObject: expectedObj];
    return YES;
}

/* Custom XCTestCase method implementations. These implementations simply return whatever values have been
 * associated with the receiving object, using the actual method function address as a key */
static inline id int_xsm_meth_impl_name (XCTestCase *self, SEL _cmd) {
    return objc_getAssociatedObject(self, (const void *) &int_xsm_meth_impl_name);
}
static inline id int_xsm_meth_impl_cls_defaultTestSuite (id self, SEL _cmd) {
    return objc_getAssociatedObject(self, (const void *) &int_xsm_meth_impl_cls_defaultTestSuite);
}
static inline int_xsm_test_section_function_t *int_xsm_meth_impl_testEntry (XCTestCase *self, SEL _cmd) {
    return (int_xsm_test_section_function_t *) [(NSValue *) objc_getAssociatedObject(self, (const void *) &int_xsm_meth_impl_testEntry) pointerValue];
}
static inline void int_xsm_meth_impl_xsmTestSection (XCTestCase *self, SEL _cmd) {
    NSSet *tags = objc_getAssociatedObject(self, (const void *) &int_xsm_meth_impl_xsmTestSection);
    int_xsm_test_section_function_t *target = int_xsm_meth_impl_testEntry(self, _cmd);
    target(self, _cmd, [tags mutableCopy]);
}

/* Given a test case description, generate a valid Objective-C identifier. */
static inline NSString *int_xsm_normalize_identifier (NSString *description) {
    /* Split the description into individual components */
    NSArray *components = [description componentsSeparatedByCharactersInSet: [NSCharacterSet whitespaceAndNewlineCharacterSet]];
    
    /* Camel case any elements that contain only lowercase letters (otherwise, we assume the case is already correct), and remove
     * any invalid characters that may not occur in an Objective-C identifier. */
    NSMutableArray *cleanedComponents = [NSMutableArray arrayWithCapacity: [components count]];
    NSCharacterSet *allowedChars = [NSCharacterSet characterSetWithCharactersInString: @"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"];
    for (NSUInteger i = 0; i < [components count]; i++) {
        NSString *component = components[i];
        NSString *newComponent = [[component componentsSeparatedByCharactersInSet: [allowedChars invertedSet]] componentsJoinedByString: @""];
        
        /* If the string is entirely lowercase, apply camel casing */
        if ([[newComponent lowercaseString] isEqualToString: newComponent]) {
            newComponent = [newComponent capitalizedString];
        }

        /* Add to the result array. */
        [cleanedComponents addObject: newComponent];
    }
    
    /* Generate the identifier, stripping any leading numbers */
    NSString *identifier = [cleanedComponents componentsJoinedByString: @""];
    {
        NSRange range = [identifier rangeOfCharacterFromSet: [NSCharacterSet decimalDigitCharacterSet]];
        if (range.location == 0)
            identifier = [identifier substringFromIndex: range.length];
    }
    
#ifdef INT_XSM_DEBUG
    NSLog(@"Mapped '%@' to identifier '%@'", description, identifier);
#endif

    return identifier;
}

/* Given a test case description and a target class, derive a unique selector selector from the camel cased description, and register it with the target class and imp. */
static inline SEL int_xsm_register_test_selector (Class cls, const char *description, void (*imp)(XCTestCase *self, SEL _cmd)) {
    /* Generate a valid selector for the description */
    NSString *selectorName = int_xsm_normalize_identifier([NSString stringWithUTF8String: description]);
    
    /* If the selector is already in use, loop until we have a unique name */
    while (class_getInstanceMethod(cls, NSSelectorFromString(selectorName)) != NULL) {
        for (NSUInteger i = 0; i < NSUIntegerMax; i++) {
            if (i == NSUIntegerMax) {
                [NSException raise: NSInternalInconsistencyException format: @"Couldn't find a unique selector name for %s. You must have an impressive number of tests.", description];
                __builtin_trap();
            }
            
            selectorName = [NSString stringWithFormat:@"%@%" PRIu64, selectorName, (uint64_t) i];
            if (class_getInstanceMethod(cls, NSSelectorFromString(selectorName)) == NULL)
                break;
        }
    }

    /* Register and return the SEL */
    SEL newSel = NSSelectorFromString(selectorName);
    
    { // -xsmTestSection
        NSString *typeEnc = [NSString stringWithFormat: @"%s%s%s", @encode(void), @encode(id), @encode(SEL)];
        class_addMethod(cls, newSel, (IMP) imp, [typeEnc UTF8String]);
    }

    return newSel;
}

/* Register a new class, automatically selecting a valid and unique class name based on the given description. */
static inline Class int_xsm_register_test_case_class (const char *description) {
    /* Generate a valid class name from the description */
    NSString *className = int_xsm_normalize_identifier([NSString stringWithUTF8String: description]);
    
    /* If the class name is already in use, loop until we've got a unique name */
    if (NSClassFromString(className) != nil) {
        /* First, try appending 'Tests'; this handles the case where the tests have the same name as the class being tested. */
        if (![className hasSuffix: @"Test"] && ![className hasSuffix: @"Tests"]) {
            NSString *testClassName = [className stringByAppendingString: @"Tests"];
            
            if (NSClassFromString(testClassName) == nil) {
                className = testClassName;
            }
        }
        
        /* Otherwise, try appending a unique number to the name */
        for (NSUInteger i = 0; i < NSUIntegerMax && NSClassFromString(className) != nil; i++) {
            if (i == NSUIntegerMax) {
                [NSException raise: NSInternalInconsistencyException format: @"Couldn't find a unique test name for %@. You must have an impressive number of tests.", className];
                __builtin_trap();
            }
            
            NSMutableString *proposedName = [NSMutableString stringWithFormat:@"%@%" PRIu64, className, (uint64_t) i];
            if (NSClassFromString(proposedName) == nil) {
                className = proposedName;
                break;
            }
        }
    }
    
    /* Allocate the new class */
    Class cls = objc_allocateClassPair([XCTestCase class], [className UTF8String], 0);
    if (cls == nil) {
        [NSException raise: NSInternalInconsistencyException format: @"Could not allocate test class: %@", className];
        __builtin_trap();
    }

    /* Add XCTestCase methods */
    { // +defaultTestSuite
        Method m = class_getInstanceMethod([[XCTestCase class] class], @selector(defaultTestSuite));
        class_addMethod(object_getClass(cls), @selector(defaultTestSuite), (IMP) int_xsm_meth_impl_cls_defaultTestSuite, method_getTypeEncoding(m));
    }
    
    /* Add XCTest methods */
    { // -name
        Method m = class_getInstanceMethod([[XCTestCase class] class], @selector(name));
        class_addMethod(cls, @selector(name), (IMP) int_xsm_meth_impl_name, method_getTypeEncoding(m));
    }

    /* Register the new class */
    objc_registerClassPair(cls);
    
    return cls;
}
