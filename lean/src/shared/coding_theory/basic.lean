-- Ref: Error-Correcting Linear Codes
import tactic
import analysis.normed.group.basic
import linear_algebra.finite_dimensional
import data.matrix.rank
universes u

open finite_dimensional

set_option old_structure_cmd true

structure linear_code (𝔽 : Type u) [field 𝔽] [fintype 𝔽] (n k : ℕ)
  extends codewords : submodule 𝔽 (fin n → 𝔽) :=
  (gen_mat' : ∃ (Γ : matrix (fin k) (fin n) 𝔽), Γ.rank = k ∧ ∀ c ∈ carrier, ∃ v, c = Γ.vec_mul v)

namespace linear_code

variables {𝔽 : Type u} [field 𝔽] [fintype 𝔽] {n k : ℕ} (c : fin n → 𝔽)

instance : set_like (linear_code 𝔽 n k) (fin n → 𝔽) :=
⟨linear_code.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : linear_code 𝔽 n k} : c ∈ p.carrier ↔ c ∈ (p : set (fin n → 𝔽)) := iff.rfl

@[ext] theorem ext {p q : linear_code 𝔽 n k} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

/-- Copy of a `linear_code` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : linear_code 𝔽 n k) (s : set (fin n → 𝔽)) (hs : s = ↑p) : 
linear_code 𝔽 n k :=
{ carrier := s,
  add_mem' := hs.symm ▸ p.add_mem',
  zero_mem' := hs.symm ▸ p.zero_mem',
  smul_mem' := hs.symm ▸ p.smul_mem',
  gen_mat' := hs.symm ▸ p.gen_mat' }

@[simp] lemma coe_copy (p : linear_code 𝔽 n k) (s : set (fin n → 𝔽)) (hs : s = ↑p) :
  (p.copy s hs : set (fin n → 𝔽)) = s := rfl

lemma copy_eq (p : linear_code 𝔽 n k) (s : set  ((fin n → 𝔽))) (hs : s = ↑p) : p.copy s hs = p :=
set_like.coe_injective hs

end linear_code