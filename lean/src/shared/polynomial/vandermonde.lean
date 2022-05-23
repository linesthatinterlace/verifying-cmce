import linear_algebra.vandermonde
import linear_algebra.matrix.nondegenerate
import to_mathlib.polynomial.degree_lt_le

namespace matrix
open_locale big_operators matrix
open finset
lemma det_vandermonde_ne_zero_of_injective {R : Type*} [comm_ring R] 
[is_domain R] {n : ℕ} (α : fin n ↪ R) : (vandermonde α).det ≠ 0 :=
begin
  simp_rw [det_vandermonde, prod_ne_zero_iff, mem_filter, 
  mem_univ, forall_true_left, true_and, sub_ne_zero, ne.def, 
  embedding_like.apply_eq_iff_eq],
  rintro _ _ _ rfl, apply lt_irrefl _ (by assumption)
end

theorem vandermonde_invertibility' {R : Type*} [comm_ring R]
[is_domain R] {n : ℕ} (α : fin n ↪ R) {f : fin n → R}
(h₂ : ∀ j, ∑ i : fin n, (α j ^ (i : ℕ)) * f i = 0) : f = 0
:= by {apply eq_zero_of_mul_vec_eq_zero (det_vandermonde_ne_zero_of_injective α), ext, apply h₂}

theorem vandermonde_invertibility {R : Type*} [comm_ring R]
[is_domain R] {n : ℕ}
{α : fin n ↪ R} {f : fin n → R}
(h₂ : ∀ j, ∑ i, f i * (α j ^ (i : ℕ))  = 0) : f = 0
:= by {apply vandermonde_invertibility' α, simp_rw mul_comm, exact h₂}

theorem vandermonde_invertibility_transposed {R : Type*} [comm_ring R] 
[is_domain R] {n : ℕ}
{α : fin n ↪ R} {f : fin n → R}
(h₂ : ∀ i : fin n, ∑ j : fin n, f j * (α j ^ (i : ℕ)) = 0) : f = 0
:= by {apply eq_zero_of_vec_mul_eq_zero 
(det_vandermonde_ne_zero_of_injective α), ext, apply h₂}

end matrix

namespace polynomial
open_locale polynomial big_operators

open linear_equiv matrix polynomial

theorem vandermonde_invertibility {R : Type*} [comm_ring R] [is_domain R] {n : ℕ}
(α : fin n ↪ R) (p : degree_lt R n) (h₁ : ∀ j, (p : R[X]).is_root (α j)) : p = 0 :=
begin
  simp_rw degree_lt.to_tuple_root at h₁,
  exact (degree_lt.to_tuple_eq_zero_iff p).mp (vandermonde_invertibility h₁)
end

theorem vandermonde_invertibility_tranposed {R : Type*} [comm_ring R] [is_domain R]
{n : ℕ} (α : fin n ↪ R) (p : degree_lt R n)
(h₁ : ∀ i : fin n, ∑ j : fin n, (p : R[X]).coeff j * (α j ^ (i : ℕ)) = 0) : p = 0 :=
(degree_lt.to_tuple_eq_zero_iff p).mp (vandermonde_invertibility_transposed h₁)

theorem vandermonde_agreement {R : Type*} [comm_ring R] [is_domain R] {n : ℕ}
(α : fin n ↪ R) {p q : R[X]} (h₀ : (p - q) ∈ degree_lt R n)
(h₂ : ∀ j, p.eval (α j) = q.eval (α j)) : p = q :=
begin
  rw ← sub_eq_zero, have vi := vandermonde_invertibility α ⟨p - q, h₀⟩,
  simp only [submodule.coe_mk, is_root.def, eval_sub, submodule.mk_eq_zero] at vi,
  exact vi (λ _, sub_eq_zero.mpr (h₂ _)),
end

end polynomial