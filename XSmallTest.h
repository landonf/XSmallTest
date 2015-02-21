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

#include <CoreFoundation/CoreFoundation.h>

#include <inttypes.h>

#include <objc/runtime.h>
#include <objc/message.h>

#include <mach-o/getsect.h>
#include <dlfcn.h>
#include <stdio.h>

#ifdef __OBJC__
#import <XCTest/XCTest.h>
#else
/* Compatibility types for non-ObjC operation */
typedef Class XCTestCase;
typedef Class XCTestSuite;
typedef Class XCTest;
#endif

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

/* Internal logging/error reporting API */
#define IXSM_ERROR(x, ...) int_xsm_nsfprintf(stderr, CFSTR("[XSmallTest] " x "\n"), ##__VA_ARGS__);
#define IXSM_FATAL(x, ...) do { \
    IXSM_ERROR(x, ## __VA_ARGS__); \
    abort(); \
} while(0)

#ifdef INT_XSM_DEBUG
#define IXSM_DEBUG(x, ...) int_xsm_nsfprintf(stderr, CFSTR("[XSmallTest] " x "\n"), ##__VA_ARGS__);
#else
#define IXSM_DEBUG(x, ...)
#endif

/* CFString-compatible printf() API */
CF_FORMAT_FUNCTION(2,0) int int_xsm_nsvfprintf (FILE *stream, CFStringRef format, va_list args) {
    int retval;
    
    CFStringRef str = CFStringCreateWithFormatAndArguments(NULL, NULL, format, args);
    retval = fprintf(stream, "%s", CFStringGetCStringPtr(str, kCFStringEncodingUTF8));
    CFRelease(str);
    
    return retval;
}

CF_FORMAT_FUNCTION(2,3) int int_xsm_nsfprintf (FILE *stream, CFStringRef format, ...) {
    va_list ap;
    int retval;
    
    va_start(ap, format);
    {
        retval = int_xsm_nsvfprintf(stream, format, ap);
    }
    va_end(ap);
    
    return retval;
}

CF_FORMAT_FUNCTION(1,2) int int_xsm_nsprintf (CFStringRef format, ...) {
    va_list ap;
    int retval;
    
    va_start(ap, format);
    {
        retval = int_xsm_nsvfprintf(stderr, format, ap);
    }
    va_end(ap);
    
    return retval;
}

/* Internal macro to assist in calling Objective-C methods */
#define IXSM_OBJC(ret, recv, ...) ((ret (*)(__typeof__(recv), SEL, ## __VA_ARGS__))objc_msgSend)

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
    static void int_xsm_test_func_ ## __xsm_tag (XCTestCase *self, SEL _cmd, CFMutableSetRef INT_XSM_TEST_TAGS); \
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
    static void int_xsm_test_func_ ## __xsm_tag (XCTestCase *self, SEL _cmd, CFMutableSetRef INT_XSM_TEST_TAGS)

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
#if defined(__OBJC__) && __has_feature(objc_arc)
#   define INT_XSM_RETAIN(obj)
#   define INT_XSM_RELEASE(__xsmall_obj) __xsmall_obj = nil;
#   define INT_XSM_MRC_ONLY(expr)
#else
#   define INT_XSM_RETAIN(__xsmall_obj) CFRetain((__bridge CFTypeRef) __xsmall_obj);
#   define INT_XSM_RELEASE(__xsmall_obj) do { \
        CFRelease((__bridge CFTypeRef) __xsmall_obj); \
        __xsmall_obj = nil; \
} while(0)
#   define INT_XSM_MRC_ONLY(expr) expr
#   define __bridge
#endif

/* Autorelease a CFTypeRef, preserving the self-type on return. */
#define INT_XSM_AUTORELEASE(_cfObj) ((__typeof__(_cfObj)) int_xsm_autorelease(_cfObj))

/* Internal CFAutorelease implementation */
static inline CFTypeRef int_xsm_autorelease (CFTypeRef cfObj) {
#if defined(__OBJC__) && __has_feature(objc_arc)
    extern id objc_autorelease(id);
    CFTypeRef ret = (__bridge CFTypeRef) objc_autorelease((__bridge id) cfObj);
#elif defined(__OBJC__)
    CFTypeRef ret = (__bridge CFTypeRef) [(__bridge id) cfObj autorelease];
#else
    CFTypeRef ret = ((CFTypeRef (*)(CFTypeRef self, SEL _cmd))objc_msgSend)(cfObj, sel_getUid("autorelease"));
#endif

    return ret;
}

/**
 * XSM Clause Types
 */
typedef CF_ENUM(uint16_t, xsm_clause_type_t) {
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
typedef CF_ENUM(uint16_t, xsm_section_type_t) {
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
typedef void (int_xsm_test_section_function_t)(XCTestCase *self, SEL _cmd, CFMutableSetRef tags);

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
static inline BOOL int_xsm_sect_tag_check (CFMutableSetRef tags, int expected, int parent);
static inline id int_xsm_meth_impl_cls_defaultTestSuite (id self, SEL _cmd);
static inline int_xsm_test_section_function_t *int_xsm_meth_impl_testEntry (XCTestCase *self, SEL _cmd);
static inline void int_xsm_meth_impl_xsmTestSection (XCTestCase *self, SEL _cmd);
static inline id int_xsm_meth_impl_name (XCTestCase *self, SEL _cmd);

static inline SEL int_xsm_register_test_selector (Class cls, const char *description, void (*imp)(XCTestCase *self, SEL _cmd));
static inline Class int_xsm_register_test_case_class (const char *description);

/* CoreFoundation-compatible tag comparison. */
static inline CFComparisonResult int_xsm_compare_tags (const void *lhs, const void *rhs, void *context) {
    if (lhs < rhs) {
        return kCFCompareLessThan;
    } else if (lhs > rhs) {
        return kCFCompareGreaterThan;
    } else {
        return kCFCompareEqualTo;
    }
}

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
            IXSM_FATAL("Could not find our own image!");
        }
        
        /* Fetch the section data */
#ifdef __LP64__
        xsm_sect.data = getsectiondata((const struct mach_header_64 *) dli.dli_fbase, XSM_SEG_NAME, XSM_SECT_NAME, &xsm_sect.size);
#else
        xsm_sect.data = getsectiondata((const struct mach_header *) dli.dli_fbase, XSM_SEG_NAME, XSM_SECT_NAME, &xsm_sect.size);
#endif
        
        /* This should never happen; our constructor is only called if at least a test case has been registered */
        if (xsm_sect.data == NULL) {
            IXSM_FATAL("Could not find __DATA,xsm_tests in %s", dli.dli_fname);
            __builtin_trap();
        }
        
        xsm_sect.end = (void *) ((uintptr_t)xsm_sect.data + xsm_sect.size);
    }
    
    /* Extract all registered tests */
    CFTypeRef pool = IXSM_OBJC(CFTypeRef, Class)(objc_getClass("NSAutoreleasePool"), sel_getUid("new"));
    {
        void *ptr = xsm_sect.data;

        /* Parse all records for this translation unit */
        CFMutableArrayRef tagOrder = INT_XSM_AUTORELEASE(CFArrayCreateMutable(NULL, 0, NULL)); /* tags */
        CFMutableDictionaryRef records = INT_XSM_AUTORELEASE(CFDictionaryCreateMutable(NULL, 0, NULL, NULL)); /* tag -> int_xsm_section_record ptr; */
        while (ptr != xsm_sect.end) {
            assert(ptr < xsm_sect.end);

            /* Save the record reference and advance ptr */
            int_xsm_section_record *rec = (int_xsm_section_record *) ptr;
            ptr = (void *) ((uint8_t *)ptr + rec->size);
            
            /* Skip invalid versions */
            if (rec->version != 0) {
                IXSM_ERROR("Skipping invalid XSM test record version (%hu)", rec->version);
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
            CFArrayAppendValue(tagOrder, (void *) (uintptr_t) rec->tag);
            CFDictionarySetValue(records, (void *) (uintptr_t) rec->tag, rec);

            IXSM_DEBUG("Found record %p (size=%hu, version=%hu) with type=%hu, clause=%hu, order=%u, desc=%s, parent=%u, imp=%p",
                  rec, rec->size, rec->version, rec->type, rec->clause, rec->tag, rec->description, rec->parent_tag, rec->section_imp);
        }
        
        /* Re-order the section's according to their tag order; this corresponds to the order they were declared
         * in this translation unit. */
        CFArraySortValues(tagOrder, CFRangeMake(0, CFArrayGetCount(tagOrder)), int_xsm_compare_tags, NULL);
        
        /* Fix up any parent references to the pseudo-test case tag (0). These are references to the most recently
         * defined test case. */
        {
            int_xsm_section_record *currentRoot = NULL;
            for (CFIndex i = 0; i < CFArrayGetCount(tagOrder); i++) {
                uint32_t tag = (uint32_t) (uintptr_t) ((CFArrayGetValueAtIndex(tagOrder, i)));
                int_xsm_section_record *rec = (int_xsm_section_record *) CFDictionaryGetValue(records, (void *) (uintptr_t) tag);
                
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
                    IXSM_FATAL("No parent test case was defined for section '%s'", rec->description);

                /* Fix up the ophan's parent tag reference. */
                rec->parent_tag = currentRoot->tag;
            }
        }
        
        /* Generate test cases for all tags */
        CFMutableDictionaryRef testCases = INT_XSM_AUTORELEASE(CFDictionaryCreateMutable(NULL, 0, NULL, &kCFTypeDictionaryValueCallBacks)); /* tag -> XCTestCase */
        CFMutableSetRef allParentTags = INT_XSM_AUTORELEASE(CFSetCreateMutable(NULL, 0, NULL)); /* tag -- includes all test cases that have defined children */
        {
            CFMutableArrayRef tagStack = INT_XSM_AUTORELEASE(CFArrayCreateMutable(NULL, 0, NULL));
            int_xsm_section_record *rootRecord = NULL;
            for (CFIndex i = 0; i < CFArrayGetCount(tagOrder); i++) {
                uint32_t tag = (uint32_t) (uintptr_t) ((CFArrayGetValueAtIndex(tagOrder, i)));
                int_xsm_section_record *rec = (int_xsm_section_record *) CFDictionaryGetValue(records, (void *) (uintptr_t) tag);
                
                /* Adjust our parse state for the section type. */
                switch ((xsm_section_type_t) rec->type) {
                    case XSM_SECTION_TYPE_TEST_CASE:
                        /* This is a new root node; drop our previous tag stack, and set the new root node value */
                        CFArrayRemoveAllValues(tagStack);
                        rootRecord = rec;
                        break;
                        
                    case XSM_SECTION_TYPE_NESTED: {
                        /* This is a child node; pop the stack until we hit this child's parent's tag. */
                        while (
                               CFArrayGetCount(tagStack) > 0 &&
                               CFArrayGetValueAtIndex(tagStack, CFArrayGetCount(tagStack) - 1) != (void *) (uintptr_t) rec->parent_tag)
                        {
                            CFArrayRemoveValueAtIndex(tagStack, CFArrayGetCount(tagStack) - 1);
                            assert(CFArrayGetCount(tagStack) != 0);
                        }
                        break;
                    }
                }
                
                /* At this point, there *must* be a root record in well-formed data */
                assert(rootRecord != NULL);
                
                /* Register this section on the tag stack. */
                CFArrayAppendValue(tagStack, (void *) (uintptr_t) rec->tag);

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
                CFStringRef description = NULL; // Must be deallocated after use below.
                switch ((xsm_clause_type_t) rec->clause) {
                    case XSM_CLAUSE_TYPE_GIVEN:
                        description = CFStringCreateWithFormat(NULL, NULL, CFSTR("Given %s"), rec->description);
                        break;
                    case XSM_CLAUSE_TYPE_WHEN:
                        description = CFStringCreateWithFormat(NULL, NULL, CFSTR("when %s"), rec->description);
                        break;
                    case XSM_CLAUSE_TYPE_THEN:
                        description = CFStringCreateWithFormat(NULL, NULL, CFSTR("then %s"), rec->description);
                        break;
                }
                
                /* Create a test case instance for this section */
                SEL testSel = int_xsm_register_test_selector(rec->section_class, rec->description, &int_xsm_meth_impl_xsmTestSection);
                XCTestCase *tc = IXSM_OBJC(XCTestCase *, Class, SEL)(rec->section_class, sel_getUid("testCaseWithSelector:"), testSel);

                assert(description != NULL);
                objc_setAssociatedObject((id) tc, (const void *) &int_xsm_meth_impl_name, (__bridge id) (description), OBJC_ASSOCIATION_RETAIN);
                CFRelease(description);
  
                CFMutableSetRef allTags = INT_XSM_AUTORELEASE(CFSetCreateMutable(NULL, 0, NULL));
                for (CFIndex i = 0; i < CFArrayGetCount(tagStack); i++) {
                    CFSetAddValue(allTags, CFArrayGetValueAtIndex(tagStack, i));
                }

                objc_setAssociatedObject((id) tc, (const void *) &int_xsm_meth_impl_xsmTestSection, (__bridge id) (allTags), OBJC_ASSOCIATION_RETAIN);
                objc_setAssociatedObject((id) tc, (const void *) &int_xsm_meth_impl_testEntry, (__bridge id)((void *) rec->section_imp), OBJC_ASSOCIATION_ASSIGN);
                
                CFDictionarySetValue(testCases, (void *) (uintptr_t) rec->tag, (__bridge void *) tc);
                
                /* Mark our parent as having a child */
                if (rec->parent_tag != INT_XSM_ORPHAN_TAG) {
                    CFSetAddValue(allParentTags, (void *) (uintptr_t) rec->parent_tag);
                }
            }
        }
        
        /* Export the parsed entries out to a test suite/test case instance tree. */
        {
            /* Convert all non-leaf nodes to test suites */
            for (CFIndex i = 0; i < CFArrayGetCount(tagOrder); i++) {
                uint32_t tag = (uint32_t) (uintptr_t) ((CFArrayGetValueAtIndex(tagOrder, i)));
                
                if (CFSetContainsValue(allParentTags, (void *) (uintptr_t) tag)) {
                    /* This is a non-leaf node; convert to a suite */
                    XCTestCase *tc = (__bridge XCTestCase *) CFDictionaryGetValue(testCases, (void *) (uintptr_t) tag);
                    
                    CFStringRef name = ((CFStringRef (*)(XCTestCase *, SEL)) objc_msgSend)(tc, sel_getUid("name"));
                    XCTestSuite *replacement = ((XCTestSuite *(*)(Class, SEL, CFStringRef)) objc_msgSend)(objc_getClass("XCTestSuite"), sel_getUid("testSuiteWithName:"), name);
                    
                    CFDictionarySetValue(testCases, (void *) (uintptr_t) tag, (__bridge void *) replacement);
                }
            }
            
            /* Iterate over the test cases and combine them into test suite(s) */
            int_xsm_section_record *rootRecord = NULL;
            CFMutableArrayRef testCaseTags = INT_XSM_AUTORELEASE(CFArrayCreateMutable(NULL, 0, NULL));
            XCTestSuite *rootSuite = nil;

            for (CFIndex i = 0; i < CFArrayGetCount(tagOrder); i++) {
                uint32_t tag = (uint32_t) (uintptr_t) (CFArrayGetValueAtIndex(tagOrder, i));
                int_xsm_section_record *rec = (int_xsm_section_record *) CFDictionaryGetValue(records, (void *) (uintptr_t) tag);
                
                /* Root node, reset our state */
                if (rec->parent_tag == INT_XSM_ORPHAN_TAG) {
                    XCTest *test = (__bridge XCTest *) CFDictionaryGetValue(testCases, (void *) (uintptr_t) rec->tag);
                    rootRecord = rec;
                    CFStringRef name = IXSM_OBJC(CFStringRef, XCTest *)(test, sel_getUid("name"));
                    rootSuite = IXSM_OBJC(XCTestSuite *, Class, CFStringRef)(objc_getClass("XCTestSuite"), sel_getUid("testSuiteWithName:"), name);
                    CFArrayRemoveAllValues(testCaseTags);
                    
                    /* If the root node has children, its children should be directly attached to the containing test suite */
                    if (CFSetContainsValue(allParentTags, (void *) (uintptr_t) rec->tag))
                        CFDictionarySetValue(testCases, (void *) (uintptr_t) rec->tag, (__bridge void *) rootSuite);
                } else {
                    assert(rootRecord != NULL);
                    assert(rootSuite != nil);
                }
                
                /* Include this tag in the output for the current root test case */
                CFArrayAppendValue(testCaseTags, (void *) (uintptr_t) tag);
                
                /* If this is not the final entry in this test case, nothing left to do */
                if (i + 1 < CFArrayGetCount(tagOrder)) {
                    uint32_t nextTag = (uint32_t) (uintptr_t) (CFArrayGetValueAtIndex(tagOrder, i + 1));
                    int_xsm_section_record *next = (int_xsm_section_record *) CFDictionaryGetValue(records, (void *) (uintptr_t) nextTag);
                    if (next->parent_tag != INT_XSM_ORPHAN_TAG)
                        continue;
                }

                /* We've iterated over the entire test case; nwo we can attach all children to their parent test suite. */
                for (CFIndex ti = 0; ti < CFArrayGetCount(testCaseTags); ti++) {
                    uint32_t tag = (uint32_t) (uintptr_t) (CFArrayGetValueAtIndex(testCaseTags, i));
                    int_xsm_section_record *rec = (int_xsm_section_record *) CFDictionaryGetValue(records, (void *) (uintptr_t) tag);

                    /* If this is the root node, we exclude it; it will either be included directly below if it's leaf node,
                     * or if it's not a leaf node, it simply provides an extraneous level of nesting below the root */
                    if (rec->tag == rootRecord->tag)
                        continue;
                    
                    XCTest *child = (__bridge XCTest *) CFDictionaryGetValue(testCases, (void *) (uintptr_t) rec->tag);
                    XCTestSuite *parent = (__bridge XCTestSuite *) CFDictionaryGetValue(testCases, (void *) (uintptr_t) rec->parent_tag);
                    
                    ((void (*)(XCTestSuite *, SEL, XCTest *)) objc_msgSend)(parent, sel_getUid("addTest:"), child);
                }
                
                /* Attach the new test suite to the test case's class. */
                XCTest *defaultTestSuite;
                if (!CFSetContainsValue(allParentTags, (void *) (uintptr_t) rootRecord->tag)) {
                    /* If the root node has no children, it should be used directly as the top-level suite */
                    defaultTestSuite = (__bridge XCTest *) CFDictionaryGetValue(testCases, (void *) (uintptr_t) rootRecord->tag);
                } else {
                    defaultTestSuite = rootSuite;
                }
                objc_setAssociatedObject((id) rootRecord->section_class, (const void *) &int_xsm_meth_impl_cls_defaultTestSuite, (id) defaultTestSuite, OBJC_ASSOCIATION_RETAIN);

                IXSM_DEBUG("Registered test cases: %@", testCases);

                /* Clean up state */
                rootRecord = NULL;
                rootSuite = nil;
            }
        }
        INT_XSM_RELEASE(pool);
    }
}

/* Check whether our tag is enabled, and whether we've already been run. We don't actually need the parent tag here; this is just used
 * to quiesce unused variable warnings on the parent tag, and 'unused variable was used' warnings that trigger with __attribute__((unused)) */
static inline BOOL int_xsm_sect_tag_check (CFMutableSetRef tags, int expected, int parent) {
    if (CFSetGetCount(tags) == 0 || !CFSetContainsValue(tags, (void *) (uintptr_t) expected))
        return NO;

    CFSetRemoveValue(tags, (void *) (uintptr_t) expected);
    return YES;
}

/* Custom XCTestCase method implementations. These implementations simply return whatever values have been
 * associated with the receiving object, using the actual method function address as a key */
static inline id int_xsm_meth_impl_name (XCTestCase *self, SEL _cmd) {
    return objc_getAssociatedObject((id) self, (const void *) &int_xsm_meth_impl_name);
}
static inline id int_xsm_meth_impl_cls_defaultTestSuite (id self, SEL _cmd) {
    return objc_getAssociatedObject((id) self, (const void *) &int_xsm_meth_impl_cls_defaultTestSuite);
}
static inline int_xsm_test_section_function_t *int_xsm_meth_impl_testEntry (XCTestCase *self, SEL _cmd) {
    return (int_xsm_test_section_function_t *) (__bridge void *) (objc_getAssociatedObject((id) self, (const void *) &int_xsm_meth_impl_testEntry));
}
static inline void int_xsm_meth_impl_xsmTestSection (XCTestCase *self, SEL _cmd) {
    CFSetRef tags = (__bridge CFSetRef) objc_getAssociatedObject((id) self, (const void *) &int_xsm_meth_impl_xsmTestSection);
    int_xsm_test_section_function_t *target = int_xsm_meth_impl_testEntry(self, _cmd);
    target(self, _cmd, INT_XSM_AUTORELEASE(CFSetCreateMutableCopy(NULL, 0, tags)));
}

/* Given a test case description, generate a valid Objective-C identifier. */
static inline CFStringRef int_xsm_normalize_identifier (CFStringRef description) {
    /* Split the description into individual components */
    CFCharacterSetRef wscharset = CFCharacterSetGetPredefined(kCFCharacterSetWhitespaceAndNewline);
    CFArrayRef components = IXSM_OBJC(CFArrayRef, CFStringRef, CFCharacterSetRef)(description, sel_getUid("componentsSeparatedByCharactersInSet:"), wscharset);
    
    /* Camel case any elements that contain only lowercase letters (otherwise, we assume the case is already correct), and remove
     * any invalid characters that may not occur in an Objective-C identifier. */
    CFMutableArrayRef cleanedComponents = CFArrayCreateMutable(NULL, CFArrayGetCount(components), &kCFTypeArrayCallBacks);
    CFCharacterSetRef allowedChars = IXSM_OBJC(CFCharacterSetRef, Class, CFStringRef)(objc_getClass("NSCharacterSet"), sel_getUid("characterSetWithCharactersInString:"), CFSTR("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"));
    
    for (CFIndex i = 0; i < CFArrayGetCount(components); i++) {
        CFStringRef component = (CFStringRef) CFArrayGetValueAtIndex(components, i);
        CFArrayRef newComponents = IXSM_OBJC(CFArrayRef, CFStringRef, CFCharacterSetRef)(component, sel_getUid("componentsSeparatedByCharactersInSet:"), INT_XSM_AUTORELEASE(CFCharacterSetCreateInvertedSet(NULL, allowedChars)));
        CFStringRef newComponent = IXSM_OBJC(CFStringRef, CFArrayRef, CFStringRef)(newComponents, sel_getUid("componentsJoinedByString:"), CFSTR(""));
        
        /* If the string is entirely lowercase, apply camel casing */
        CFStringRef lowerComponent = IXSM_OBJC(CFStringRef, CFStringRef)(newComponent, sel_getUid("lowercaseString"));
        if (CFEqual(lowerComponent, newComponent)) {
            newComponent = IXSM_OBJC(CFStringRef, CFStringRef)(newComponent, sel_getUid("capitalizedString"));
        }

        /* Add to the result array. */
        CFArrayAppendValue(cleanedComponents, newComponent);
    }
    
    /* Generate the identifier, stripping any leading numbers */
    CFStringRef identifier = IXSM_OBJC(CFStringRef, CFArrayRef, CFStringRef)(cleanedComponents, sel_getUid("componentsJoinedByString:"), CFSTR(""));
    {
        CFRange range = IXSM_OBJC(CFRange, CFStringRef, CFCharacterSetRef)(identifier, sel_getUid("rangeOfCharacterFromSet:"), CFCharacterSetGetPredefined(kCFCharacterSetDecimalDigit));
        if (range.location == 0)
            identifier = CFStringCreateWithSubstring(NULL, identifier, CFRangeMake(range.length, CFStringGetLength(identifier) - range.length));
    }
    
    IXSM_DEBUG("Mapped '%@' to identifier '%@'", description, identifier);

    return identifier;
}

/* Given a test case description and a target class, derive a unique selector selector from the camel cased description, and register it with the target class and imp. */
static inline SEL int_xsm_register_test_selector (Class cls, const char *description, void (*imp)(XCTestCase *self, SEL _cmd)) {
    /* Generate a valid selector for the description */
    CFStringRef selectorName = int_xsm_normalize_identifier(INT_XSM_AUTORELEASE(CFStringCreateWithCString(NULL, description, kCFStringEncodingUTF8)));
    
    /* If the selector is already in use, loop until we have a unique name */
    while (class_getInstanceMethod(cls, sel_getUid(CFStringGetCStringPtr(selectorName, kCFStringEncodingUTF8))) != NULL) {
        for (size_t i = 0; i < SIZE_T_MAX; i++) {
            if (i == SIZE_T_MAX) {
                IXSM_FATAL("Couldn't find a unique selector name for %s. You must have an impressive number of tests.", description);
                __builtin_trap();
            }
            
            selectorName = INT_XSM_AUTORELEASE(CFStringCreateWithFormat(NULL, NULL, CFSTR("%@%" PRIu64), selectorName, (uint64_t) i));
            if (class_getInstanceMethod(cls, sel_getUid(CFStringGetCStringPtr(selectorName, kCFStringEncodingUTF8))) == NULL)
                break;
        }
    }

    /* Register and return the SEL */
    SEL newSel = sel_getUid(CFStringGetCStringPtr(selectorName, kCFStringEncodingUTF8));
    
    { // -xsmTestSection
        CFStringRef typeEnc = CFSTR("v@:");
        class_addMethod(cls, newSel, (IMP) imp, CFStringGetCStringPtr(typeEnc, kCFStringEncodingUTF8));
    }

    return newSel;
}

/* Register a new class, automatically selecting a valid and unique class name based on the given description. */
static inline Class int_xsm_register_test_case_class (const char *description) {
    /* Generate a valid class name from the description */
    CFStringRef className = int_xsm_normalize_identifier(INT_XSM_AUTORELEASE(CFStringCreateWithCString(NULL, description, kCFStringEncodingUTF8)));
    
    /* If the class name is already in use, loop until we've got a unique name */
    if (objc_getClass(CFStringGetCStringPtr(className, kCFStringEncodingUTF8)) != NULL) {
        /* First, try appending 'Tests'; this handles the case where the tests have the same name as the class being tested. */
        if (!CFStringHasSuffix(className, CFSTR("Test")) && !CFStringHasSuffix(className, CFSTR("Tests"))) {
            CFStringRef testClassName = INT_XSM_AUTORELEASE(CFStringCreateWithFormat(NULL, NULL, CFSTR("%@%@"), className, CFSTR("Tests")));
            
            if (CFStringGetCStringPtr(testClassName, kCFStringEncodingUTF8) == nil) {
                className = testClassName;
            }
        }
        
        /* Otherwise, try appending a unique number to the name */
        for (size_t i = 0; i < SIZE_T_MAX && objc_getClass(CFStringGetCStringPtr(className, kCFStringEncodingUTF8)) != nil; i++) {
            if (i == SIZE_T_MAX) {
                IXSM_FATAL("Couldn't find a unique test name for %@. You must have an impressive number of tests.", className);
                __builtin_trap();
            }
            
            CFStringRef proposedName = INT_XSM_AUTORELEASE(CFStringCreateWithFormat(NULL, NULL, CFSTR("%@%" PRIu64), className, (uint64_t) i));
            if (objc_getClass(CFStringGetCStringPtr(proposedName, kCFStringEncodingUTF8)) == nil) {
                className = proposedName;
                break;
            }
        }
    }
    
    /* Allocate the new class */
    Class cls = objc_allocateClassPair(objc_getClass("XCTestCase"), CFStringGetCStringPtr(className, kCFStringEncodingUTF8), 0);
    if (cls == nil) {
        IXSM_FATAL("Could not allocate test class: %@", className);
        __builtin_trap();
    }

    /* Add XCTestCase methods */
    { // +defaultTestSuite
        Method m = class_getInstanceMethod(objc_getMetaClass("XCTestCase"), sel_getUid("defaultTestSuite"));
        class_addMethod(object_getClass((id) cls), sel_getUid("defaultTestSuite"), (IMP) int_xsm_meth_impl_cls_defaultTestSuite, method_getTypeEncoding(m));
    }
    
    /* Add XCTest methods */
    { // -name
        Method m = class_getInstanceMethod(objc_getMetaClass("XCTestCase"), sel_getUid("name"));
        class_addMethod(cls, sel_getUid("name"), (IMP) int_xsm_meth_impl_name, method_getTypeEncoding(m));
    }

    /* Register the new class */
    objc_registerClassPair(cls);
    
    return cls;
}
