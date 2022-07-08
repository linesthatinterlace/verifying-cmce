import linear_algebra.vandermonde
import linear_algebra.matrix.nondegenerate
import .degree_lt_le

namespace matrix
open_locale big_operators matrix
open finset

theorem vandermonde_invertibility' {R : Type*} [comm_ring R]
[is_domain R] {n : ℕ} {α : fin n → R} (hα : function.injective α) {f : fin n → R}
(h₂ : ∀ j, ∑ i : fin n, (α j ^ (i : ℕ)) * f i = 0) : f = 0
:= eq_zero_of_mul_vec_eq_zero (det_vandermonde_ne_zero_iff.mpr hα) (funext h₂)

theorem vandermonde_invertibility {R : Type*} [comm_ring R]
[is_domain R] {n : ℕ} {α : fin n → R} (hα : function.injective α) {f : fin n → R}
(h₂ : ∀ j, ∑ i, f i * (α j ^ (i : ℕ)) = 0) : f = 0
:= by {refine vandermonde_invertibility' hα _, simp_rw mul_comm, exact h₂}

theorem vandermonde_invertibility_transposed {R : Type*} [comm_ring R] 
[is_domain R] {n : ℕ}
{α : fin n → R} (hα : function.injective α) {f : fin n → R}
(h₂ : ∀ i : fin n, ∑ j : fin n, f j * (α j ^ (i : ℕ)) = 0) : f = 0
:= eq_zero_of_vec_mul_eq_zero (det_vandermonde_ne_zero_iff.mpr hα) (funext h₂)

end matrix

namespace polynomial
open_locale polynomial big_operators

open linear_equiv matrix polynomial

theorem vandermonde_invertibility {R : Type*} [comm_ring R] [is_domain R] {n : ℕ}
(α : fin n ↪ R) {p : R[X]} (hp₁ : p ∈ degree_lt R n)
(hp₂ : ∀ j, eval (α j) p = 0) : p = 0 :=
begin
  rw degree_lt.to_tuple_eq_zero_iff hp₁,
  refine vandermonde_invertibility α.inj' (λ j, _), specialize hp₂ j,
  rw degree_lt.to_tuple_equiv_eval hp₁ at hp₂, exact hp₂
end

theorem vandermonde_invertibility_transposed {R : Type*} [comm_ring R] [is_domain R]
{n : ℕ} (α : fin n ↪ R) (p : degree_lt R n)
(hp : ∀ i : fin n, ∑ j : fin n, (p : R[X]).coeff j * (α j ^ (i : ℕ)) = 0) : p = 0 :=
(degree_lt.to_tuple_eq_zero_iff p).mp (vandermonde_invertibility_transposed hα hp)

theorem vandermonde_agreement {R : Type*} [comm_ring R] [is_domain R] {n : ℕ}
{α : fin n → R} (hα : function.injective α) {p q : R[X]} (hpq₁ : (p - q) ∈ degree_lt R n)
(hpq₂ : ∀ j, p.eval (α j) = q.eval (α j)) : p = q :=
begin
  rw ← sub_eq_zero, have vi := vandermonde_invertibility hα ⟨p - q, hpq₁⟩,
  simp only [submodule.coe_mk, is_root.def, eval_sub, submodule.mk_eq_zero] at vi,
  exact vi (λ _, sub_eq_zero.mpr (hpq₂ _))
end

end polynomial