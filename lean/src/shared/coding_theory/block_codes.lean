import tactic
import data.nat.log

import .hamming

namespace finset
instance decidable_nonempty (α : Type*) (s : finset α) : decidable (s.nonempty) :=
decidable_of_iff (0 < s.card) card_pos
end finset

structure block_code {ι : Type*} (β : ι → Type*) := 
(codewords : finset (hamm β))

namespace block_code
open finset function

section set_like

variables {ι : Type*} {β : ι → Type*} {c : hamm β}

instance : set_like (block_code β) (hamm β) :=
⟨coe ∘ block_code.codewords, λ C D h, by { cases C, cases D, simpa [finset.coe_inj] using h }⟩

instance : has_coe_t (block_code β) (finset (hamm β)) := ⟨block_code.codewords⟩

@[simp, norm_cast] lemma mem_coe {c : hamm β} {C : block_code β} : 
  c ∈ (C : finset (hamm β)) ↔ c ∈ C := iff.rfl

@[simp] lemma coe_mem {C : block_code β} (x : (C : finset (hamm β))) : ↑x ∈ C := x.2

@[simp] lemma mk_coe {C : block_code β} (x : (C : finset (hamm β))) {h} :
  (⟨x, h⟩ : (C : finset (hamm β))) = x := subtype.coe_eta _ _

instance decidable_mem [fintype ι] [Π i, decidable_eq (β i)] (c : hamm β) (C : block_code β) :
  decidable (c ∈ C) := finset.decidable_mem' _ _

@[ext] theorem ext {C D : block_code β} (h : ∀ x, x ∈ C ↔ x ∈ D) : C = D := set_like.ext h

@[simp, norm_cast] theorem coe_inj {s₁ s₂ : block_code β} : (s₁ : finset (hamm β)) = s₂ ↔ s₁ = s₂ :=
by simp_rw [finset.ext_iff, set_like.ext_iff, mem_coe]

lemma coe_injective : injective (coe : block_code β → (finset (hamm β))) := λ s t, coe_inj.1

end set_like

section main

variables {ι : Type*} {β : ι → Type*}

instance : inhabited (block_code β) := ⟨⟨∅⟩⟩

def size (C : block_code β) := (C : finset (hamm β)).card

variables [fintype ι] [Π i, decidable_eq (β i)] {C : block_code β}

def nontrivial (C : block_code β) : Prop := (C : finset (hamm β)).off_diag.nonempty

instance : decidable (C.nontrivial) := 
decidable_of_iff C.codewords.off_diag.nonempty iff.rfl

lemma nontrivial_iff_exists_distinct : C.nontrivial ↔ ∃ x y ∈ C, x ≠ y :=
by simp_rw [  nontrivial, nonempty_iff_ne_empty, ne.def, ext_iff, mem_off_diag,
              mem_coe, not_mem_empty, iff_false, not_and,
              not_not, not_forall, exists_prop, prod.exists, exists_and_distrib_left ]

lemma trivial_iff_forall_eq : ¬ C.nontrivial ↔ ∀ x y ∈ C, x = y :=
by simp_rw [nontrivial_iff_exists_distinct, not_exists, not_not]

def min_dist (C : block_code β) :=
if H : C.nontrivial then C.codewords.off_diag.inf' H (function.uncurry hamm_dist) else 0

lemma min_dist_eq_zero_of_trivial (h : ¬ C.nontrivial) : C.min_dist = 0 := dif_neg h

lemma min_dist_ne_zero_of_nontrivial (h : C.nontrivial) : C.min_dist ≠ 0 := 
begin
  simp_rw [min_dist, dif_pos h, ← zero_lt_iff, lt_inf'_iff],rintros ⟨x, y⟩ hxy,
  rw [function.uncurry_apply_pair, hamm_dist_pos], rw mem_off_diag at hxy, exact hxy.2.2
end

@[simp] lemma min_dist_ne_zero_iff_nontrivial : ¬ C.min_dist = 0 ↔ C.nontrivial := 
⟨ λ h, by { contrapose! h, exact min_dist_eq_zero_of_trivial h }, min_dist_ne_zero_of_nontrivial⟩

lemma min_dist_eq_zero_iff_trivial :
  C.min_dist = 0 ↔ ¬C.nontrivial := min_dist_ne_zero_iff_nontrivial.not_right

lemma min_dist_eq_zero_iff_forall_dist_eq_zero :
  C.min_dist = 0 ↔ ∀ x y ∈ C, hamm_dist x y = 0 :=
by { simp_rw [min_dist_eq_zero_iff_trivial, trivial_iff_forall_eq, hamm_dist_eq_zero], refl }

lemma min_dist_le_iff_exists_dist_le {d : ℕ} (hC : C.nontrivial) :  C.min_dist ≤ d.succ ↔ 
  ∃ (x y ∈ C), x ≠ y ∧ hamm_dist x y ≤ d.succ :=
begin
  simp_rw [min_dist, dif_pos hC, inf'_le_iff, mem_off_diag],
  exact ⟨ λ ⟨_, ⟨hx, hy, hxy⟩, hxyd⟩, ⟨_, hx, _, hy, hxy, hxyd⟩,
          λ ⟨_, hx, _, hy, hxy, hxyd⟩, ⟨⟨_, _⟩, ⟨hx, hy, hxy⟩, hxyd⟩ ⟩
end

lemma lt_min_dist_of_forall_lt_dist {d : ℕ} (hC : C.nontrivial) : d < C.min_dist ↔ 
  ∀ (x y ∈ C), x ≠ y → d < hamm_dist x y :=
begin
  simp_rw [min_dist, dif_pos hC, lt_inf'_iff, mem_off_diag], 
  exact ⟨ λ H _ hx _ hy hxy, H ⟨_, _⟩ ⟨hx, hy, hxy⟩,
          λ H _ ⟨hx, hy, hxy⟩, H _ hx _ hy hxy ⟩
end

lemma min_dist_eq_succ_of_exists_eq_forall_lt_dist {d : ℕ} : 
  C.min_dist = d.succ → (∃ x y ∈ C, x ≠ y ∧ hamm_dist x y = d.succ) ∧ 
  ∀ x y ∈ C, x ≠ y → d < hamm_dist x y :=
begin
  by_cases hC : C.nontrivial,
  { simp_rw [ le_antisymm_iff, nat.succ_le_iff, lt_min_dist_of_forall_lt_dist hC,
              min_dist_le_iff_exists_dist_le hC],
    exact λ ⟨⟨_, hx, _, hy, hxy, hxyd⟩, H⟩, ⟨⟨_, hx, _, hy, hxy, hxyd, H _ hx _ hy hxy⟩, H⟩
  },
  { rw ← min_dist_eq_zero_iff_trivial at hC, intro H, rw H at hC, exact nat.no_confusion hC }
end

lemma exists_eq_forall_lt_dist_of_min_dist_eq_succ {d : ℕ} : 
( (∃ x y ∈ C, x ≠ y ∧ hamm_dist x y = d.succ) ∧ 
  ∀ x y ∈ C, x ≠ y → d < hamm_dist x y) → C.min_dist = d.succ  :=
begin
  by_cases hC : C.nontrivial,
  { simp_rw [ le_antisymm_iff, nat.succ_le_iff, lt_min_dist_of_forall_lt_dist hC,
              min_dist_le_iff_exists_dist_le hC], 
    exact λ ⟨⟨_, hx, _, hy, hxy, hxyd⟩, H⟩, ⟨⟨_, hx, _, hy, hxy, hxyd.1⟩, H⟩
  },
  { rw trivial_iff_forall_eq at hC, rintro ⟨⟨x, hx, y, hy, hxy, _⟩, _⟩,
    exact false.elim (hxy (hC x hx y hy)) }
end

lemma min_dist_eq_succ_iff_exists_eq_forall_lt_dist {d : ℕ} : 
  C.min_dist = d.succ ↔ (∃ x y ∈ C, x ≠ y ∧ hamm_dist x y = d.succ) ∧ 
  ∀ x y ∈ C, x ≠ y → d < hamm_dist x y :=
⟨min_dist_eq_succ_of_exists_eq_forall_lt_dist, exists_eq_forall_lt_dist_of_min_dist_eq_succ⟩

end main

end block_code
#lint