import ring_theory.polynomial.basic

namespace polynomial
open_locale polynomial big_operators

open submodule

noncomputable def degree_le' (R : Type*) [semiring R] (n : with_bot ℕ) : submodule R R[X] :=
⨅ k : ℕ, ⨅ h : n < ↑k, (lcoeff R k).ker

theorem mem_degree_le'  {R : Type*} [semiring R] {n : with_bot ℕ} {f : R[X]} :
  f ∈ degree_le' R n ↔ degree f ≤ n :=
by simp only [ degree_le', submodule.mem_infi, degree_le_iff_coeff_zero, linear_map.mem_ker]; refl 

namespace degree_le

lemma bot_eq (R : Type*) [semiring R] : degree_le R ⊥ = degree_lt R 0 := 
by simp_rw [degree_le, degree_lt, ge_iff_le, gt_iff_lt, with_bot.bot_lt_coe, zero_le']

lemma nat_eq (R : Type*) [semiring R] (n : ℕ) : degree_le R n = degree_lt R (n + 1) :=
by simp_rw [degree_le, degree_lt, ge_iff_le, gt_iff_lt, with_bot.coe_lt_coe]; refl

end degree_le

namespace degree_lt

noncomputable def to_tuple {R : Type*} [comm_ring R] {n : ℕ} (p : degree_lt R n) :
fin n → R := degree_lt_equiv _ _ p

lemma to_tuple_eq {R : Type*} [comm_ring R] {n : ℕ} (p : degree_lt R n) :
to_tuple p = (degree_lt_equiv _ _) p := rfl

lemma to_tuple_apply {R : Type*} [comm_ring R] {n : ℕ} (p : degree_lt R n) (i : fin n) :
to_tuple p i = (p : R[X]).coeff i := rfl

theorem to_tuple_eq_zero_iff {R : Type*} [comm_ring R] {n : ℕ} (p : degree_lt R n) :
to_tuple p = 0 ↔ p = 0 := by rw [to_tuple_eq, linear_equiv.map_eq_zero_iff]

theorem to_tuple_eq_iff {R : Type*} [comm_ring R] {n : ℕ} (p q : degree_lt R n) :
to_tuple p = to_tuple q ↔ p = q :=
by {  simp_rw [to_tuple_eq, (linear_equiv.injective _).eq_iff] }

theorem to_tuple_equiv_eval {R : Type*} [comm_ring R] {n : ℕ} (p : degree_lt R n) (x : R) :
∑ i, to_tuple p i * (x ^ (i : ℕ)) = (p : R[X]).eval x :=
begin
  simp_rw [to_tuple_apply, eval_eq_sum],
  exact sum_fin (λ e a, a * x ^ e) (λ i, zero_mul (x ^ i)) (mem_degree_lt.mp (coe_mem _))
end

theorem to_tuple_root {R : Type*} [comm_ring R] {n : ℕ} (p : degree_lt R n) (x : R) :
(p : R[X]).is_root x ↔ ∑ i, to_tuple p i * (x ^ (i : ℕ)) = 0
:= by rw [is_root.def, to_tuple_equiv_eval]

/-
theorem degree_lt_rank {F : Type*} [field F] {t : ℕ} : module.rank F (degree_lt F t) = t := by {rw (degree_lt_equiv' F t).dim_eq, exact dim_fin_fun _}

theorem degree_lt_finrank {F : Type*} [field F] {t : ℕ} : finite_dimensional.finrank F (degree_lt F t) = t := finite_dimensional.finrank_eq_of_dim_eq degree_lt_rank
-/

end degree_lt

end polynomial