import .block_codes

set_option old_structure_cmd true

structure linear_code {ι : Type*} (α : Type*) [semiring α] (β : ι → Type*) 
  [Π i, add_comm_monoid (β i)] [Π i, module α (β i)] extends block_code β :=
(add_mem' : ∀ {a b}, a ∈ codewords → b ∈ codewords → a + b ∈ codewords)
(zero_mem' : (0 : hamm β) ∈ codewords)
(smul_mem' : ∀ (c : α) {a}, a ∈ codewords → c • a ∈ codewords)

namespace linear_code

section set_like

variables {ι : Type*} {α : Type*} [semiring α] {β : ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, module α (β i)]

instance : set_like (linear_code α β) (hamm β) :=
⟨coe ∘ linear_code.codewords, λ C D h, by { cases C, cases D, simpa [finset.coe_inj] using h }⟩

@[simp] lemma mem_codewords {C : linear_code α β} {c : hamm β} : 
  c ∈ C.codewords ↔ c ∈ (C : set (hamm β)) := iff.rfl

@[ext] theorem ext {C D : linear_code α β} (h : ∀ x, x ∈ C ↔ x ∈ D) : C = D := set_like.ext h

/-- Copy of a `linear_code` with a new `codewords` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : linear_code α β) (s : finset (hamm β)) (hs : (s : set (hamm β)) = ↑p) : linear_code α β :=
{ codewords := s,
  add_mem' := begin simp_rw ← finset.mem_coe, simp_rw hs, simp, end,
  zero_mem' := hs.symm ▸ p.zero_mem',
  smul_mem' := hs.symm ▸ p.smul_mem' }

@[simp] lemma coe_copy (p : linear_code α β) (s : finset (hamm β)) (hs : s = ↑p) :
  (p.copy s hs : finset (hamm β)) = s := rfl

lemma copy_eq (p : linear_code α β) (s : finset (hamm β)) (hs : s = ↑p) : p.copy s hs = p :=
finset_like.coe_injective hs

end set_like

open finset

variables {ι : Type*} {α : Type*} [semiring α] {β : ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, module α (β i)]

variables {ι : Type*} (α : Type*) [semiring α] (β : ι → Type*) 
variables [Π i, add_comm_monoid (β i)] [Π i, module α (β i)] {C : linear_code α β}

protected lemma zero_mem : (0 : hamm β) ∈ C := C.zero_mem'
protected lemma add_mem {a b} (ha : a ∈ C) (hb : b ∈ C) : 
  a + b ∈ C := C.add_mem' ha hb
protected lemma smul_mem (r : α) {a} (ha : a ∈ C) : r • a ∈ C :=
C.smul_mem' _ ha

instance : inhabited (linear_code α β) := 
⟨ { codewords := {0},
    add_mem'  := by { simp_rw mem_singleton, rintros _ _ rfl rfl, exact zero_add _ },
    zero_mem' := by rw mem_singleton,
    smul_mem' := by { simp_rw mem_singleton, rintros _ _ rfl, exact smul_zero _ } } ⟩

def to_submodule : submodule α (hamm β) := 
{ codewords := C.codewords,
  add_mem' := begin refine λ _ _ _ _, _, refine C.add_mem _ _, end ,
  zero_mem' := _,
  smul_mem' := _ }

end linear_code

#lint