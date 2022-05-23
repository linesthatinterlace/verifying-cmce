import data.polynomial.derivative
import data.polynomial.monic
import data.polynomial.ring_division

namespace multiset
open_locale polynomial
open polynomial

noncomputable def to_polynomial {K : Type*} [comm_ring K] (A : multiset K) : K[X] :=
(A.map (λ t, X - C t)).prod

end multiset

namespace polynomial
open_locale polynomial
open multiset

variables {K : Type*} {A B : multiset K} {a : K}

section ring
variables [ring K] 

@[simp]
lemma X_sub_C_derivative : (X - C a).derivative = 1 :=
by simp only [derivative_sub, derivative_X, derivative_C, sub_zero]

end ring

section comm_semiring
variables [comm_semiring K] {p q : K[X]}

theorem bernoulli_rule_left (h : p.is_root a)
: (p*q).derivative.eval a = p.derivative.eval a * q.eval a :=
by { rw is_root.def at h, simp_rw [derivative_mul, eval_add, eval_mul, h, zero_mul, add_zero] }

theorem bernoulli_rule_right (h : q.is_root a)
: (p*q).derivative.eval a = q.derivative.eval a * p.eval a :=
by { rw [mul_comm, bernoulli_rule_left h] }

end comm_semiring

section comm_ring
variables [comm_ring K] 


lemma to_polynomial_eq : A.to_polynomial = (A.map (λ t, X - C t)).prod := rfl

lemma to_polynomial_monotone (h : A ≤ B) : A.to_polynomial ∣ B.to_polynomial :=
prod_dvd_prod_of_le (map_le_map h)

lemma to_polynomial_add : (A + B).to_polynomial = (A.to_polynomial) * (B.to_polynomial) :=
by simp only [to_polynomial_eq, multiset.map_add, prod_add]


@[simp]
lemma to_polynomial_zero_eq_one : (0 : multiset K).to_polynomial = 1 := rfl

@[simp]
lemma to_polynomial_cons_eq_mul_X_sub_C_to_polynomial :
(a ::ₘ A).to_polynomial = ((X - C a) * A.to_polynomial) := 
by simp only [to_polynomial_eq, map_cons, prod_cons]

lemma to_polynomial_eq_remove [decidable_eq K] :
∀ {a : K}, a ∈ A → A.to_polynomial = (X - C a) * (A.erase a).to_polynomial := 
begin
  refine multiset.induction_on A _ _,
  { simp only [not_mem_zero, forall_false_left, forall_const] },
  { rintros a' A' IH a h, rw [mem_cons, or_iff_not_imp_left] at h,
    by_cases haa' : (a' ≠ a), 
    { simp [haa'], rw IH (h haa'.symm), ring },
    { push_neg at haa', simp [haa'] }
  }
end

lemma to_polynomial_deriative_eval_eq  [decidable_eq K] (ha : a ∈ A) :
eval a (A.to_polynomial).derivative = eval a (A.erase a).to_polynomial := 
begin
  rw [to_polynomial_eq_remove ha, bernoulli_rule_left (root_X_sub_C.mpr (eq.refl a))],
  simp only [X_sub_C_derivative, eval_one, one_mul]
end

lemma to_polynomial_monic : A.to_polynomial.monic :=
begin
  refine multiset.induction_on A _ _,
  { simp only [to_polynomial_zero_eq_one, monic_one] },
  { simp_rw [to_polynomial_cons_eq_mul_X_sub_C_to_polynomial],
    exact λ _ _ _, monic.mul (monic_X_sub_C _) (by assumption) }
end

section nontrivial
variables [nontrivial K]

lemma to_polynomial_ne_zero : A.to_polynomial ≠ 0 := to_polynomial_monic.ne_zero

open with_bot

lemma to_polynomial_splits : A.to_polynomial.degree = A.card :=
begin
  refine multiset.induction_on A _ _,
  { simp only [to_polynomial_zero_eq_one, degree_one, card_zero, coe_zero] },
  { simp only [to_polynomial_cons_eq_mul_X_sub_C_to_polynomial, card_cons], rintros _ _ h,
    rw [  mul_comm, monic.degree_mul (monic_X_sub_C _), h,
          degree_X_sub_C, with_bot.coe_add, coe_one] }
end

end nontrivial

end comm_ring

section integral_domain
variables [comm_ring K] [is_domain K] {p : K[X]}

lemma to_polynomial_roots_id : A.to_polynomial.roots = A :=
begin
  refine multiset.induction_on A _ _,
  { simp only [to_polynomial_eq, multiset.map_zero, prod_zero, roots_one, empty_eq_zero] },
  rintros, rw [to_polynomial_cons_eq_mul_X_sub_C_to_polynomial, roots_mul],
              { simpa only [roots_mul, singleton_add, roots_X_sub_C, cons_inj_right] },
              { exact (monic_X_sub_C _).mul_right_ne_zero (to_polynomial_ne_zero) }
end

lemma roots_le_of_dvd_to_polynomial (h : p ∣ A.to_polynomial) : p.roots ≤ A := 
by { rw ← @to_polynomial_roots_id _ A, exact roots.le_of_dvd (to_polynomial_ne_zero) h }

lemma roots_of_polt (h₁ : p ∣ A.to_polynomial) (h₂ : p.monic) : p = p.roots.to_polynomial := 
begin
  sorry
end

lemma dvd_to_polynomial_iff [decidable_eq K] {p : K[X]} : p ∣ A.to_polynomial ↔ p = (C p.leading_coeff) * (A ∩ p.roots).to_polynomial :=
begin
  sorry
end

end integral_domain

section field
variables [field K]

lemma to_polynomial_div_eq [decidable_eq K] (ha : a ∈ A) :
A.to_polynomial / (X - C a) = (A.erase a).to_polynomial := 
by { rw [to_polynomial_eq_remove ha, euclidean_domain.mul_div_cancel_left], apply X_sub_C_ne_zero }

end field

end polynomial