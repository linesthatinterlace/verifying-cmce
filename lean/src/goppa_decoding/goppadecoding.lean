-- https://cr.yp.to/papers/goppadecoding-20220320.pdf
import tactic
import data.polynomial.basic
import linear_algebra.lagrange
import shared.with_bot_top
import shared.polynomial.degree_lt_le
import shared.linear_algebra.basic
import shared.polynomial.vandermonde
import shared.polynomial.misc
import linear_algebra.dimension
import algebra.big_operators.basic
-- Section 2 (Polynomials)
/-
Much of this section is straightforwardly in mathlib. Imports are given (though
some may be redundant), and where there is a wrinkle to do with the way Lean
represents things, it's noted.
-/
section gdtwo

-- 2.1 (Commutative rings)
/-
Provided by the comm_ring structure. Note that there is a theory of semirings,
not-necessarily-commutative rings, etc. also.

import algebra.ring.basic
-/

-- 2.2 Ring morphisms
/-
Provided by the ring_hom structure (which extends multiplicative and additive 
homomorphisms). This gives additive and multiplicative identity preservation,
and distribution over the operations. Preservation of additive inverse is given
by ring_hom.map_neg.

import algebra.ring.basic
-/

-- 2.3 Multiples
/-
This is simply about ideals and their generators. This is probably best given by
ideal.span (which defines the ideal which is generated by a ring). There are a
collection of span_singleton lemmas for the special case where the generating
set is a singleton (a principal ideal). There is a theorem of principal ideal
domains but this seems not necessary here.

import ring_theory.ideal.basic
-/

-- 2.4 Units
/-
The definition of a (multiplicative) unit is given by the is_unit predicate.
units M is the structure which contains the units of a monoid M in a bundled way
(that is, something of type units M contains the unit, its inverse, and proofs
that they form a left-sided and right-sided unit pair). units M is not a set - 
you cannot talk about a ∈ units M, but given some a : M (where we have [ring M]),
if you have a hypothesis of type is_unit a, that contains the u : units M whose
coercion is a, so you can extract it. 

import algebra.group.units
-/

-- 2.5 Fields
/-
Given by the field structure. The is_field predicate expresses that a ring is a
field; the is_field.to_field definition noncomputably takes a proof that a 
ring R is a field and gives the field structure resulting.

import algebra.field.basic

-/

-- 2.6 Vector space
/-
A vector space is a module over a field. Lean does not have a separate notion of
a vector space, and so the module structure (which corresponds to a semimodule
in regular maths - i.e. it can be defined over a semiring) is used for it.

There is a lot of subtlety here that is not relevant outside of the original 
algebraic context, and so other imports might be needed. Handle with care.

import algebra.module.basic
-/

-- 2.7 Standard n-dimensional vector space.
/-
A complicated issue because in full generality these structure can have
complicated indexing and so much is given in a high level of abstraction.
On top of that, finiteness can be a tricky issue when trying to do stuff
correctly. It might be that actually want you want is matrix.std_basis
or matrix.std_basis_matrix, as this could give you the matrix basis for the
special case of rows and columns. You need to think carefully about what is
meant here.

If you just want row vectors, incidentally, the ![a, b, ..., z] notation
introduced by data.fin.vec_notation will suffice, as these are things to which
matrices can be applied.

The following should give the required notation and the basis stuff. But here
be dragons if you aren't careful.

import data.matrix.basis
import data.matrix.notation
-/

-- 2.8 Linear maps
/-
The linear_map structure of algebra.module.linear_map is the abstract version of
this.

finrank_le_finrank_of_injective is the theorem that if a linear map between
two finite-dimensional spaces is injective, the dimension of the domain
is less than or equal to the dimension of the codomain. The converse implies
that when the domain has a greater dimension than the codomain, there is some
non-zero vector which maps to zero. One can also look at this using the
rank-nullity theorem, finrank_range_add_finrank_ker.

The theory of finite-dimensional spaces is obviously full of particular
theorems, and is covered by linear_algebra.finite_dimensional.

import algebra.module.linear_map
import linear_algebra.finite_dimensional
-/

-- 2.9 Polynomials
/-
Polynomials over a ring R are really just finitely-supported maps from R to
ℕ, along with the structure that retains the structure of R for addition and
scalar multiplication and defines products using convolution. This is an
additive monoid algebra, and so secretly this is just what a polynomial is
in Lean. However, data.basic provides a good API and notation so that
we mostly don't have to worry about any of this.

Note that polynomials are not (currently) implemented in a computable way -
that is, the definition of polynomials is sufficiently abstracted that it
requires classical choice. This might change at some point (because it is
not ideal...)

import data.polynomial.basic

-/

-- 2.10 The ring-structure of polynomials
/-
As mentioned, the commutative ring structure on polynomials over a commutative
ring is virtually present by definition. semiring is the core
instance - there are various other instances for generalisations or different
ways to view the structure.
-/

-- 2.11 The k-algebra structure of polynomials
/-
The C map is the constant map from R to R[X]. This is the algebra 
map. The instance algebra_of_algebra shows that A[X] is an R-algebra
when A is an R-algebra, which gives the special case when A = R, and API is
provided for working with this.

import data.algebra_map
-/

-- 2.12 Units of k[x]
/-
The theorem is_unit_iff characterises the units of R[X], where R is 
commutative domain, as the embedding of the units of R. When R is not a domain
but simply a commutative semiring, it is still true that a member of R is a unit
iff its embedding is (is_unit_C). (Consider (2X + 1)*(2X + 1) when R
is Z/(4) - 2X + 1 is a unit without degree 0. The issue turns out to be that
deg(f*g) = deg f * deg g for non-zero f, g may not be true in the presence of
zero divisors.)

import data.polynomial.ring_division
-/

-- 2.13 The k-vector structure of polynomials
/-
We have module as an instance, and it's definitionally equal to the
instance of module that arises from the instance of polynomials as an algebra
under the base ring - so from Lean's point of view these are the same.

import data.polynomial.basic
-/

-- 2.14 Powers of x
/-
monomial n a is the monomial a*X^n. We have sum_monomial_eq which tells us that
a polynomial is equal to the sum over its coefficients f_i of f_i*X^i (Lean
provides sum to do this kind of summation: internally this is a 
finset.sum. This is as opposed to a finsum, which is the infinite sum over
finite non-zero values mentioned in the paper: for various reasons there are a
few different ways of doing finite sums but this is the way polynomial does 
things). We also have from this a way of doing induction on polynomials by 
proving an additive fact for monomials.

import data.polynomial.induction

-/

-- 2.15 Coefficients
/-
coeff p n gives the nth coefficient of n in p, where n : ℕ. Extending
this to ℤ would not be too hard; what the appropriate decision in 4.1 would
be is yet to be answered.

import data.polynomial.basic
-/

-- 2.16 Degree
/-
We have both degree and nat_degree (which differ in how
they handle the zero polynomial). There are a good number of theorems for these.

import data.polynomial.basic
-/


-- 2.17 Monic polynomials
/-
There is a monic predicate.

import data.degree.definitions
-/

-- 2.18 Evaluation
/-
eval exists, though it is non-computable so you can prove theorems
about it but not actually evaluate computationally.

import data.polynomial.basic
-/
-- 2.19 Roots
/-
roots gives a multiset of the polynomial's roots,
including multiplicity. It does not have a meaningful definition for the zero
polynomial!

import data.polynomial.basic
-/
-- 2.20 Vandermonde invertibility
/-
This derives from card_roots, which is a version of it though not
in the equivalent form.

However, it is also true separately from polynomial theory.
-/

-- 2.21 Transposed Vandermonde inequality
/-
Easily proved.
-/

-- 2.22 Derivatives
/-
derivative is the formal derivative of a  The product 
rule is proven for it. Bernoulli's rule is not proven for it, but this shouldn't
be too difficult.

import data.derivative
-/


-- 2.23 Quotients and remainders
/-
There is a notion of polynomial division and modulo, but also polynomial
is a Euclidean domain which gives the q/r decomposition.
-/
-- 2.24 Unique Factorisation
/-
We have an instance of unique_factorization_monoid for polynomial, and it follows
from the Euclidean domain stuff.

-/
-- 2.25 Greatest common divisors
/-
Follows from Euclidean domain.
-/

-- 2.26 Squarefreeness
/-
separable.squarefree precisely gives that a polynomial is squarefree
if it is separable - which is exactly that it is coprime with its formal derivative.

import field_theory.separable
-/

end gdtwo

/-

namespace polynomial

universes u y v

variables {R : Type u} [comm_semiring R] {ι : Type y}

open_locale polynomial classical big_operators

theorem derivative_prod' {s : finset ι} {f : ι → R[X]} :
  derivative (∏ b in s, f b) = ∑ b in s, (∏ a in (s.erase b), f a) * (f b).derivative := derivative_prod

end polynomial
-/

section gdthree
open_locale polynomial big_operators

noncomputable theory

open polynomial fintype lagrange

variables {F ι : Type*} [field F] [fintype ι] [decidable_eq ι] (α : ι ↪ F) (r : ι → F) (f : F[X])

--3.1
theorem three_one : (f.degree < card ι ∧ ∀ i, f.eval (α i) = r i) ↔ 
f = ∑ i, C (r i) * (∏ j, ite (j ≠ i) (C ((α i) - (α j))⁻¹ * (X - C (α j)))) 1 := sorry

-- 3.2 - "three_three is correct"
-- 3.3 - an alternative construction of the interpolation. 
-- We do not make complexity claims.
-- 3.4 - no specific theorem

def nodal : F[X] := ∏ y in s, (X - C y)

lemma nodal_eq_remove {x : F} (hx : x ∈ s) : nodal s = (X - C x) * (∏ y in s.erase x, (X - C y)) := by {rw mul_prod_erase _ _ hx, refl}

lemma nodal_derive_eval_node_eq {x : F} (hx : x ∈ s) : eval x (nodal s).derivative = ∏ y in (s.erase x), (x - y) := 
begin
  rw [nodal_eq_remove _ hx, bernoulli_rule (root_X_sub_C.mpr rfl)],
  simp_rw [eval_prod, derivative_sub, derivative_X, derivative_C, sub_zero, eval_one, one_mul, eval_sub, eval_X, eval_C]
end

lemma nodal_div_eq {x : F} (hx : x ∈ s) :
nodal s / (X - C x) = (∏ y in s.erase x, (X - C y)) := 
begin
  rw [nodal_eq_remove _ hx, euclidean_domain.mul_div_cancel_left],
  apply X_sub_C_ne_zero,
end

lemma basis_eq_nodal_div_eval_deriv_mul_linear {x : F} (hx : x ∈ s) : basis s x = C (eval x (nodal s).derivative)⁻¹ * (nodal s / (X - C x))  :=
begin
  rw lagrange.basis,
  rw [nodal_div_eq _ hx, nodal_derive_eval_node_eq _ hx, prod_mul_distrib, ← prod_inv_distrib, map_prod]
end

lemma interpolate_eq_derivative_interpolate (f : F → F) : interpolate s f = ∑ x in s, C (f x * (eval x (nodal s).derivative)⁻¹) * (nodal s / (X - C x)) :=
begin
  apply sum_congr rfl, intros _ hx,
  rw [C.map_mul, basis_eq_nodal_div_eval_deriv_mul_linear _ hx, mul_assoc]
end

/-- Lagrange interpolation: given a finset `s` and a function `f : F → F`,
`interpolate s f` is the unique polynomial of degree `< s.card`
that takes value `f x` on all `x` in `s`. -/
def interpolate' (r : s → F) : F[X] := ∑ x : s, C (r x) * basis s x

end gdthree

section gdfour
open_locale classical polynomial 

open polynomial linear_map algebra

def approximant_error {R : Type*} [comm_ring R] (A B : R[X]) : R[X] × R[X] →ₗ[R] R[X] := 
coprod (lmul_right _ B) (lmul_right _ (-A))

def approximant_quotient {R : Type*} [comm_ring R] {a b A B : R[X]}
{n : ℕ} (hA : A ∈ degree_le R n) (hB : B ∈ degree_lt R n)
{t : ℕ} (ha : a ∈ degree_le R t) (hb : b ∈ degree_lt R t) : 
R[X] × R[X] →ₗ[R] R[X] ⧸ degree_lt R (n - t) := 
(degree_lt R (n - t)).mkq.comp (approximant_error A B)

lemma approximant_error_apply {R : Type*} [comm_ring R] {A B a b : R[X]} : approximant_error A B (a, b) = a*B - b*A := by {simp only [approximant_error, coprod_apply, lmul_right_apply], ring }

lemma mul_sub_mul_degree_lt_add_of_degrees_le_lt_le_lt {R : Type*} [comm_ring R] [no_zero_divisors R] {a b A B : R[X]} {n t : ℕ}
(hA : A.degree ≤ n) (hB : B.degree < n) (ha : a.degree ≤ t) (hb : b.degree < t)
: (a*B - b*A).degree < t + n := 
begin
  have h : (a * B - b * A).degree ≤ max (a.degree + B.degree) (b.degree + A.degree),
    exact le_trans (degree_sub_le _ _) (le_of_eq (by simp only [degree_mul])),
  rw [le_max_iff] at h, cases h; apply lt_of_le_of_lt h,
  exact with_bot.add_lt_add_of_le_of_lt_of_right_ne_bot (with_bot.coe_ne_bot) ha hB,
  exact with_bot.add_lt_add_of_lt_of_le_of_right_ne_bot (with_bot.coe_ne_bot) hb hA
end

theorem approximate_error_bounded_degree
{R : Type*} [comm_ring R] [no_zero_divisors R] {A B : R[X]}
{n : ℕ} (hA : A ∈ degree_le R n) (hB : B ∈ degree_lt R n) (t : ℕ) :
∀ ab : R[X] × R[X], ab ∈ (degree_le R t).prod (degree_lt R t) →
(approximant_error A B) ab ∈ degree_lt R (t + n) := 
begin
  simp only [ mem_degree_lt, mem_degree_le, approximant_error_apply,
              submodule.mem_prod, and_imp, prod.forall] at *,
  intros a b ha hb,
  exact mul_sub_mul_degree_lt_add_of_degrees_le_lt_le_lt hA hB ha hb
end

def approximant_error_restricted {R : Type*} [comm_ring R] [no_zero_divisors R] {A B : R[X]}
{n : ℕ} (hA : A ∈ degree_le R n) (hB : B ∈ degree_lt R n) (t : ℕ) :
(degree_le R t).prod (degree_lt R t) →ₗ[R] degree_lt R (t + n) :=
linear_map.restrict' _ (approximate_error_bounded_degree hA hB _)

theorem comap_nontrivial {K : Type*} {V : Type*} {V₂ : Type*} [field K]
[add_comm_group V] [module K V] [add_comm_group V₂] [module K V₂] 
(f : V →ₗ[K] V₂) {q : submodule K V₂}
(hq : (module.rank K V₂) < (module.rank K q) + (module.rank K V) ) : ∃ x ≠ 0, f x ∈ q :=
begin
  suffices H : submodule.comap f q ≠ ⊥,
  { rcases submodule.exists_mem_ne_zero_of_ne_bot H with ⟨x, hf, hx⟩,
    exact ⟨x, hx, hf⟩
  },
  intro H, apply not_le_of_lt hq,
  have range_disjoint : q ⊓ f.range = ⊥, by rw [inf_comm, ← linear_map.comap_le_ker_iff, H]; exact bot_le,
  have ker_trivial : f.ker = ⊥, by rw eq_bot_iff; exact le_trans (linear_map.ker_le_comap) H.le,
  convert linear_map.dim_le_of_injective _ (submodule.injective_subtype (q ⊔ f.range)),
  rw [  ← congr_arg ((+) (module.rank K ↥q)) (dim_range_add_dim_ker f),
        ker_trivial, ←add_assoc, ← dim_sup_add_dim_inf_eq, range_disjoint],
  simp_rw [dim_bot, add_zero]
end

--4.1
theorem four_one (t : ℕ) {k : Type*} [field k] {A B : k[X]} (hAB : B.degree < A.degree) : ∃ a b : k[X], gcd a b = 1 ∧ a.degree ≤ t ∧ b.degree < t ∧ (a*B - b*A).degree + t < A.degree := sorry

--4.2
theorem four_two (t : ℕ) {k : Type*} [field k] {A B a b c d : k[X]} (hab : gcd a b = 1) (ha : a.degree ≤ t) (haBbA : (a*B - b*A).degree + t < A.degree) (hc : c.degree ≤ t) (hcBdA : (c*B - d*A).degree + t < A.degree) : ∃ p : k[X], c = p*a ∧ d = p*b := sorry

-- 4.3 and 4.4: algorithm and proof of correctness,
-- constructing a b from t, k, A,B.

--  4.5 offers a different way to construct a, b. Complexity questions do not occupy us.

-- 4.6 - "you can reformulate the above in terms of approximants"

-- 4.7 - Defines approximants. Probably best to use (a version of) this in the above 
-- theorems. Note the very general definition!

-- 4.8 - History. Not relevant.

end gdfour

section gdfive

-- 5.1 - Hamming weight. Implemented elsewhere.

-- 5.2, 5.3 - an interpolation w/ errors algorithm

-- 5.4 We can state this but not nicely. Basically a statement about approximants!

-- 5.5 Seems to be the contrapositive of 5.4 to some degree?

-- 5.6 Could be tricky because formally needs the power series object.

-- 5.7 Links the above to R-S codes.

-- 5.8 Defines R-S codes.

-- 5.9 Extensive history

end gdfive

section gdsix

-- 6.1, 6.2 Algorithm

-- 6.3 Goppa square codes.

-- 6.4 Goppa decoding works

-- 6.5 How to check Goppa decoding

-- 6.6 mostly just remarks?

end gdsix

section gdseven

-- 7.1 Overview

-- 7.2 Looks like a horrible proof and might need 5.6

-- 7.3 Getting increasingly hard to see what is being claimed.

-- 7.4 Checking Goppa decoding for F2_^n

end gdseven

section gdeight

-- 8.1 CMcE ciphertexts

-- 8.2 CMcE decryption

-- 8.3 "Rigidity", not defined, but is about recognising valid inputs.

-- 8.4 comment about robust system design

-- 8.5 history

end gdeight