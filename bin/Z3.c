/*
 * Z3.c
 *
 *  Created on: 2012/9/2
 *      Author: Chen-yi Kao
 */

#include <stdio.h>
#include <stdlib.h>
#include <z3.h>


/**
 * Copied from test_capi.c#exitf()
 */
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
 * Copied from test_capi.c#error_handler()
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

/**
 * Copied from test_capi.c#mk_var()
 */
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
 * Copied from test_capi.c#mk_context_custom()
 */
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "MODEL", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}

/**
 * Copied from test_capi.c#mk_context()
 */
Z3_context mk_context()
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

/**
 * Copied from test_capi.c#mk_int_var()
 */
Z3_ast mk_int_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
 * Copied from test_capi.c#check()
 */
void check(Z3_context ctx, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (m) {
        Z3_del_model(ctx, m);
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
}



/**
 * Find a model for the race constraint:
 *
 * (declare-fun tM () Int)
 * (declare-fun chunk () Int)
 *
 * (declare-fun gx () Int)
 * (declare-fun tx () Int)
 * (declare-fun ix () Int)
 * (declare-fun jx () Int)
 * (declare-fun gy () Int)
 * (declare-fun ty () Int)
 * (declare-fun iy () Int)
 *
 * (declare-fun k () Int)
 * (declare-fun size () Int)
 *
 * ; (k+1)+(gx*tM+tx)*chunk <= ix < (k+1)+(gx*tM+tx+1)*chunk
 * (assert (<= (+ (+ k 1) (* (+ (* gx tM) tx) chunk) ix)))
 * (assert (< ix (+ (+ k 1) (* (+ (+ (* gx tM) tx) 1) chunk))))
 *
 * ; (k+1)+(gy*tM+ty)*chunk <= iy < (k+1)+(gy*tM+ty+1)*chunk
 * (assert (<= (+ (+ k 1) (* (+ (* gy tM) ty) chunk) iy)))
 * (assert (< iy (+ (+ k 1) (* (+ (+ (* gy tM) ty) 1) chunk))))
 *
 * (assert (not (= tx ty)))
 * (assert (<= 0 tx))
 * (assert (< tx tM))
 * (assert (<= 0 ty))
 * (assert (< ty tM))
 * (assert (< 0 chunk))
 * (assert (<= 0 gx))
 * (assert (<= 0 gy))
 *
 * ; k + 1 <= ix < size
 * (assert (<= (+ k 1) ix))
 * (assert (< ix size))
 *
 * ; k + 1 <= jx < size
 * (assert (<= (+ k 1) jx))
 * (assert (< jx size))
 * (assert (= k 1))
 *
 * ; k + 1 < iy < size - 1
 * (assert (< (+ k 1) iy))
 * (assert (< iy (- size 1)))
 *
 * ; ix = iy - 1
 * (assert (= ix (- iy 1)))
 *
 */
int main(void) {

    Z3_context ctx = mk_context();


//    RACE CONSTRAINT: PARALLEL CONDITION
    Z3_ast tM, chunk, k, gx, tx, ix, jx, gy, ty, iy;

//    (declare-fun tM () Int)
//    (declare-fun chunk () Int)
    tM      = mk_int_var(ctx, "tM");
    chunk	= mk_int_var(ctx, "chunk");

//    (declare-fun k () Int)
//    (declare-fun gx () Int)
//    (declare-fun tx () Int)
//    (declare-fun ix () Int)
//    (declare-fun jx () Int)
//    (declare-fun gy () Int)
//    (declare-fun ty () Int)
//    (declare-fun iy () Int)
    k		= mk_int_var(ctx, "k");
    gx      = mk_int_var(ctx, "gx");
    tx		= mk_int_var(ctx, "tx");
    ix      = mk_int_var(ctx, "ix");
    jx		= mk_int_var(ctx, "jx");
    gy      = mk_int_var(ctx, "gy");
    ty      = mk_int_var(ctx, "ty");
    iy      = mk_int_var(ctx, "iy");

//    ; (k+1)+(gx*tM+tx)*chunk <= ix < (k+1)+(gx*tM+tx+1)*chunk
    Z3_ast const Z3_INT_ONE 			= Z3_mk_int(ctx, 1, Z3_mk_int_sort(ctx));
    Z3_ast const k_1[] 					= {k, Z3_INT_ONE};
    Z3_ast kPlus1						= Z3_mk_add(ctx, 2, k_1);
    Z3_ast const gx_tM[] 				= {gx, tM};
    Z3_ast const gx_tM_tx[] 			= {Z3_mk_mul(ctx, 2, gx_tM), tx};
    Z3_ast const gx_tM_tx_chunk[]		= {Z3_mk_add(ctx, 2, gx_tM_tx), chunk};
    Z3_ast const k_1_gx_tM_tx_chunk[]	= {kPlus1, Z3_mk_mul(ctx, 2, gx_tM_tx_chunk)};
    Z3_ast legalIxBegin					= Z3_mk_add(ctx, 2, k_1_gx_tM_tx_chunk);
    Z3_ast const k_1_gx_tM_tx_1_chunk[] = {kPlus1, legalIxBegin, chunk};
    Z3_ast legalIxEndPlusOne			= Z3_mk_add(ctx, 3, k_1_gx_tM_tx_1_chunk);

//    (assert (<= (+ (+ k 1) (* (+ (* gx tM) tx) chunk) ix)))
//    (assert (< ix (+ (+ k 1) (* (+ (+ (* gx tM) tx) 1) chunk))))
    Z3_assert_cnstr(ctx, Z3_mk_ge(ctx, legalIxBegin, ix));
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, ix, legalIxEndPlusOne));

//    ; (k+1)+(gy*tM+ty)*chunk <= iy < (k+1)+(gy*tM+ty+1)*chunk
    Z3_ast const gy_tM[] 				= {gy, tM};
    Z3_ast const gy_tM_ty[] 			= {Z3_mk_mul(ctx, 2, gy_tM), ty};
    Z3_ast const gy_tM_ty_chunk[]		= {Z3_mk_add(ctx, 2, gy_tM_ty), chunk};
    Z3_ast const k_1_gy_tM_ty_chunk[]	= {kPlus1, Z3_mk_mul(ctx, 2, gy_tM_ty_chunk)};
    Z3_ast legalIyBegin					= Z3_mk_add(ctx, 2, k_1_gy_tM_ty_chunk);
    Z3_ast const k_1_gy_tM_ty_1_chunk[] = {kPlus1, legalIxBegin, chunk};
    Z3_ast legalIyEndPlusOne			= Z3_mk_add(ctx, 3, k_1_gy_tM_ty_1_chunk);

//    (assert (<= (+ (+ k 1) (* (+ (* gy tM) ty) chunk) iy)))
//    (assert (< iy (+ (+ k 1) (* (+ (+ (* gy tM) ty) 1) chunk))))
    Z3_assert_cnstr(ctx, Z3_mk_ge(ctx, legalIyBegin, iy));
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, iy, legalIyEndPlusOne));

//    (assert (not (= tx ty)))
//    (assert (<= 0 tx))
//    (assert (< tx tM))
//    (assert (<= 0 ty))
//    (assert (< ty tM))
//    (assert (< 0 chunk))
//    (assert (<= 0 gx))
//    (assert (<= 0 gy))
    Z3_ast const Z3_INT_ZERO = Z3_mk_int(ctx, 0, Z3_mk_int_sort(ctx));
    Z3_assert_cnstr(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, tx, ty)));
    Z3_assert_cnstr(ctx, Z3_mk_le(ctx, Z3_INT_ZERO, tx));
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, tx, tM));
    Z3_assert_cnstr(ctx, Z3_mk_le(ctx, Z3_INT_ZERO, ty));
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, ty, tM));
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, Z3_INT_ZERO, chunk));
    Z3_assert_cnstr(ctx, Z3_mk_le(ctx, Z3_INT_ZERO, gx));
    Z3_assert_cnstr(ctx, Z3_mk_le(ctx, Z3_INT_ZERO, gy));


//    RACE CONSTRAINT: PATH CONDITION
    Z3_ast size;

//    (declare-fun size () Int)
	size	= mk_int_var(ctx, "size");

//    ; k + 1 <= ix < size
//    (assert (<= (+ k 1) ix))
//    (assert (< ix size))
    Z3_assert_cnstr(ctx, Z3_mk_le(ctx, kPlus1, ix));
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, ix, size));

//    ; k + 1 <= jx < size
//    (assert (<= (+ k 1) jx))
//    (assert (< jx size))
//    (assert (= k 1))
    Z3_assert_cnstr(ctx, Z3_mk_le(ctx, kPlus1, jx));
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, jx, size));
    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, k, Z3_INT_ONE));

//    ; k + 1 < iy < size - 1
//    (assert (< (+ k 1) iy))
//    (assert (< iy (- size 1)))
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, kPlus1, iy));
    Z3_ast const size_1[] 		= {size, Z3_INT_ONE};
    Z3_assert_cnstr(ctx, Z3_mk_lt(ctx, iy, Z3_mk_sub(ctx, 2, size_1)));

//    ; ix = iy - 1
//    (assert (= ix (- iy 1)))
    Z3_ast const iy_1[] 		= {iy, Z3_INT_ONE};
    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, ix, Z3_mk_sub(ctx, 2, iy_1)));


    printf("model:\n");
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);

	return EXIT_SUCCESS;



	//const char* RACE_CONSTRAINT =
	//		"(declare-fun tM () Int) (declare-fun chunk () Int) (declare-fun gx () Int) (declare-fun tx () Int) (declare-fun ix () Int) (declare-fun jx () Int) (declare-fun gy () Int) (declare-fun ty () Int) (declare-fun iy () Int) (declare-fun k () Int) (declare-fun size () Int) (assert (<= (* (+ (* gx tM) tx) chunk) ix)) (assert (< ix (* (+ (+ (* gx tM) tx) 1) chunk))) (assert (<= (* (+ (* gy tM) ty) chunk) iy)) (assert (< iy (* (+ (+ (* gy tM) ty) 1) chunk))) (assert (not (= tx ty))) (assert (<= 0 tx)) (assert (< tx tM)) (assert (<= 0 ty)) (assert (< ty tM)) (assert (< 0 chunk)) (assert (<= 0 gx)) (assert (<= 0 gy)) (assert (<= (+ k 1) ix)) (assert (< ix size)) (assert (<= (+ k 1) jx)) (assert (< jx size)) (assert (= k 1)) (assert (< (+ k 1) iy)) (assert (< iy (- size 1))) (assert (= ix (- iy 1))) (check-sat)";

//    Z3_config  cfg;
//	Z3_context ctx;
//    Z3_ast fs;
//    Z3_solver sol;
//
//	cfg = Z3_mk_config();
//	Z3_set_param_value(cfg, "MODEL", "true");
//	ctx = Z3_mk_context(cfg);
//    sol = Z3_mk_solver(ctx);
//
//    fs  = Z3_parse_smtlib2_string(ctx, RACE_CONSTRAINT, 0, 0, 0, 0, 0, 0);
////    fs  = Z3_parse_smtlib2_file(ctx, "race.smt2", 0, 0, 0, 0, 0, 0);
//    printf("formulas: %s\n", Z3_ast_to_string(ctx, fs));
//
//    Z3_solver_inc_ref(ctx, sol);
//    printf("solver: %s\n", Z3_solver_get_help(ctx, sol));
//    Z3_model m;
//    switch (Z3_solver_check(ctx, sol)) {
//    case Z3_L_FALSE:
//        printf("unsat\n");
//		printf("unsat proof: %s\n", Z3_ast_to_string(ctx, Z3_solver_get_proof(ctx, sol)));
//        break;
//    case Z3_L_UNDEF:
//        m = Z3_solver_get_model(ctx, sol);
//        printf("unknown\n");
//        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
//        break;
//    case Z3_L_TRUE:
//        m = Z3_solver_get_model(ctx, sol);
//        printf("sat\n");
//        printf("model:\n%s\n%s", Z3_model_to_string(ctx, m), "END?");
////        printf("sat\n%s\n%s", Z3_solver_to_string(ctx, sol), "END?");
//        break;
//    }
//
////    Z3_del_context(ctx);
////	Z3_del_config(cfg);
}

