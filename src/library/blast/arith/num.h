/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/simplifier/simplifier.h"
#include "util/numerics/mpq.h"

namespace lean {
namespace blast {

/* Convert to Lean expressions */
expr mpz_to_expr(mpz const & n, expr const & A);
expr mpq_to_expr(mpq const & n, expr const & A);

/* Convert from Lean expressions */
mpq expr_to_mpq(expr const &);

/* Given a positive numeral [n], returns a proof that [0 < (n:A)] */
expr prove_positive(mpz const & n, expr const & A);
expr prove_positive(mpq const & n, expr const & A);

/* Prove a contradiction */
expr prove_zero_not_lt_zero(expr const & A);
expr prove_zero_not_lt_neg(expr const & A, mpq const & nc);
expr prove_zero_not_le_neg(expr const & A, mpq const & nc);

/* Testers */
bool is_mulinv(expr const & e);
bool is_mulinv(expr const & e, expr & n, expr & d);
bool is_mulinv_alt(expr const & e, expr & n, expr & d_inv);

bool is_numeral_expr(expr const & e);

/* Simplify */
simp::result simplify_numeral_expr(expr const & e);

/* Setup and teardown */
void initialize_num();
void finalize_num();

}}
