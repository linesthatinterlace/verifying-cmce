import .block_codes

set_option old_structure_cmd true

structure linear_code {ι : Type*} (α : Type*) [semiring α] (β : ι → Type*) 
  [Π i, add_comm_monoid (β i)] [Π i, module α (β i)] extends block_code β :=
(add_mem' : ∀ {a b}, a ∈ codewords → b ∈ codewords → a + b ∈ codewords)
(zero_mem' : (0 : hamm β) ∈ codewords)
(smul_mem' : ∀ (c : α) {a}, a ∈ codewords → c • a ∈ codewords)

namespace linear_code
open finset function

section set_like

variables {ι : Type*} {α : Type*} [semiring α] {β : ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, module α (β i)]

instance : set_like (linear_code α β) (hamm β) :=
⟨coe ∘ linear_code.codewords, λ C D h, by { cases C, cases D, simpa [finset.coe_inj] using h }⟩

instance : has_coe_t (linear_code α β) (finset (hamm β)) := ⟨linear_code.codewords⟩

@[simp, norm_cast] lemma mem_coe {c : hamm β} {C : linear_code α β} : 
  c ∈ (C : finset (hamm β)) ↔ c ∈ C := iff.rfl

instance decidable_mem [fintype ι] [Π i, decidable_eq (β i)] (c : hamm β) (C : linear_code α β) :
  decidable (c ∈ C) := finset.decidable_mem' _ _

@[ext] theorem ext {C D : linear_code α β} (h : ∀ x, x ∈ C ↔ x ∈ D) : C = D := set_like.ext h

@[simp, norm_cast] theorem coe_inj {s₁ s₂ : linear_code α β} :
  (s₁ : finset (hamm β)) = s₂ ↔ s₁ = s₂ := by simp_rw [finset.ext_iff, set_like.ext_iff, mem_coe]

lemma coe_injective : function.injective (coe : linear_code α β → (finset (hamm β))) := 
λ s t, coe_inj.1

/-- Copy of a `linear_code` with a new `codewords` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : linear_code α β) (s : finset (hamm β)) (hs : s = p) : 
  linear_code α β :=
{ codewords := s,
  add_mem' := hs.symm ▸ p.add_mem',
  zero_mem' := hs.symm ▸ p.zero_mem',
  smul_mem' := hs.symm ▸ p.smul_mem' }

@[simp] lemma coe_copy (p : linear_code α β) (s : finset (hamm β)) (hs : s = p) :
  (p.copy s hs : finset (hamm β)) = s := rfl

lemma copy_eq (p : linear_code α β) (s : finset (hamm β)) (hs : s = ↑p) : p.copy s hs = p :=
coe_injective hs

lemma coe_coe {C : linear_code α β} : ((C : finset (hamm β)) : set (hamm β)) = C := rfl

end set_like

variables {ι : Type*} {α : Type*} [semiring α] {β : ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, module α (β i)] {C : linear_code α β}

protected lemma zero_mem : (0 : hamm β) ∈ C := C.zero_mem'
protected lemma add_mem {a b} (ha : a ∈ C) (hb : b ∈ C) : a + b ∈ C := C.add_mem' ha hb
protected lemma smul_mem (r : α) {a} (ha : a ∈ C) : r • a ∈ C := C.smul_mem' _ ha

instance : inhabited (linear_code α β) := 
⟨ { codewords := {0},
    add_mem'  := by { simp_rw mem_singleton, rintros _ _ rfl rfl, exact zero_add _ },
    zero_mem' := by rw mem_singleton,
    smul_mem' := by { simp_rw mem_singleton, rintros _ _ rfl, exact smul_zero _ } } ⟩

def to_submodule : submodule α (hamm β) := 
{ carrier := C,
  add_mem' := λ _ _, linear_code.add_mem,
  zero_mem' := linear_code.zero_mem,
  smul_mem' := λ _ _, linear_code.smul_mem _ }

noncomputable def of_submodule {C : submodule α (hamm β)} (hC : (C : set (hamm β)).finite) :    
  linear_code α β :=
{ codewords := hC.to_finset,
  add_mem' := λ _ _, by { simp_rw set.finite.mem_to_finset, exact C.add_mem },
  zero_mem' := by { simp_rw set.finite.mem_to_finset, exact C.zero_mem },
  smul_mem' := λ _ _, by { simp_rw set.finite.mem_to_finset, exact C.smul_mem _ } }

lemma mem_of_mem_of_submodule {C : submodule α (hamm β)} (hC : (C : set (hamm β)).finite)
  (x : hamm β) : x ∈ C ↔ x ∈ of_submodule hC :=
begin
  rw of_submodule, cases C, simp only [submodule.mem_mk], rw set_like.has_mem, 
end


end linear_code