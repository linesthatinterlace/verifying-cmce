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

noncomputable def to_tuple {R : Type*} [comm_ring R] {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n) : fin n → R := degree_lt_equiv _ _ ⟨p, hp⟩

lemma to_tuple_eq {R : Type*} [comm_ring R] {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n)  :
to_tuple hp = (degree_lt_equiv _ _) ⟨p, hp⟩ := rfl

lemma to_tuple_apply {R : Type*} [comm_ring R] {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n)
  (i : fin n) : to_tuple hp i = p.coeff i := rfl

theorem to_tuple_eq_zero_iff {R : Type*} [comm_ring R] {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n) :
  p = 0 ↔ to_tuple hp = 0 :=
by {rw [to_tuple_eq, linear_equiv.map_eq_zero_iff, submodule.mk_eq_zero]}

theorem to_tuple_eq_iff {R : Type*} [comm_ring R] {n : ℕ} {p q : R[X]}
  (hp : p ∈ degree_lt R n) (hq : q ∈ degree_lt R n) : p = q ↔ to_tuple hp = to_tuple hq :=
by {  simp_rw [to_tuple_eq, (linear_equiv.injective _).eq_iff] }

theorem to_tuple_equiv_eval {R : Type*} [comm_ring R] {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n)
  (x : R) : p.eval x = ∑ i, to_tuple hp i * (x ^ (i : ℕ)) :=
begin
  simp_rw [to_tuple_apply, eval_eq_sum],
  rw ←sum_fin _ _ (mem_degree_lt.mp hp), simp_rw [zero_mul, forall_const]
end

theorem to_tuple_root {R : Type*} [comm_ring R] {n : ℕ} {p : R[X]} (hp : p ∈ degree_lt R n)
  (x : R) : p.is_root x ↔ ∑ i, to_tuple hp i * (x ^ (i : ℕ)) = 0
:= by rw [is_root.def, to_tuple_equiv_eval]

end degree_lt

end polynomial