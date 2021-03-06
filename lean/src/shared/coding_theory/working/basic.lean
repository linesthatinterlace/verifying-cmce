-- Ref: Error-Correcting Linear Codes
import tactic
import analysis.normed.group.basic
import linear_algebra.finite_dimensional
import data.matrix.rank
universes u

open finite_dimensional

set_option old_structure_cmd true

structure linear_code (π½ : Type u) [field π½] [fintype π½] (n k : β)
  extends codewords : submodule π½ (fin n β π½) :=
  (gen_mat' : β (Ξ : matrix (fin k) (fin n) π½), Ξ.rank = k β§ β c β carrier, β v, c = Ξ.vec_mul v)

namespace linear_code

variables {π½ : Type u} [field π½] [fintype π½] {n k : β} (c : fin n β π½)

instance : set_like (linear_code π½ n k) (fin n β π½) :=
β¨linear_code.carrier, Ξ» p q h, by cases p; cases q; congr'β©

@[simp] lemma mem_carrier {p : linear_code π½ n k} : c β p.carrier β c β (p : set (fin n β π½)) := iff.rfl

@[ext] theorem ext {p q : linear_code π½ n k} (h : β x, x β p β x β q) : p = q := set_like.ext h

/-- Copy of a `linear_code` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : linear_code π½ n k) (s : set (fin n β π½)) (hs : s = βp) : 
linear_code π½ n k :=
{ carrier := s,
  add_mem' := hs.symm βΈ p.add_mem',
  zero_mem' := hs.symm βΈ p.zero_mem',
  smul_mem' := hs.symm βΈ p.smul_mem',
  gen_mat' := hs.symm βΈ p.gen_mat' }

@[simp] lemma coe_copy (p : linear_code π½ n k) (s : set (fin n β π½)) (hs : s = βp) :
  (p.copy s hs : set (fin n β π½)) = s := rfl

lemma copy_eq (p : linear_code π½ n k) (s : set  ((fin n β π½))) (hs : s = βp) : p.copy s hs = p :=
set_like.coe_injective hs

end linear_code