import tactic
import data.nat.lattice

import .hamming
import .finset_like

namespace finset
instance decidable_nonempty (α : Type*) {s : finset α} : decidable (s.nonempty) :=
decidable_of_iff (∃ a ∈ s, true) $ by simp_rw [exists_prop, and_true, finset.nonempty]
end finset

namespace coding

open finset function
variables {ι : Type*} {β : ι → Type*} {s s' : finset (hamming β)} {c : hamming β} 
{S : Type*} {C C' : S} [i : finset_like S (hamming β)]

include i

@[reducible] def codewords (C : S) := (C : finset (hamming β))

lemma mem_codewords : c ∈ codewords C ↔ c ∈ C := finset_like.mem_coe

lemma codewords_eq_coe : (codewords : S → finset (hamming β)) = coe := rfl

@[reducible] def size (C : S) := finset.card (codewords C)

variables [fintype ι] [Π i, decidable_eq (β i)]

def nontrivial (C : S) : Prop := (codewords C).off_diag.nonempty

instance : decidable (nontrivial C) := 
decidable_of_iff (codewords C).off_diag.nonempty iff.rfl

lemma nontrivial_iff_one_lt_size : 1 < size C ↔ nontrivial C :=
by simp_rw [ nontrivial, size, one_lt_card, nonempty_iff_ne_empty, ne.def, ext_iff, mem_off_diag, 
            not_forall, not_mem_empty, iff_false, not_not, exists_prop, prod.exists, 
            exists_and_distrib_left ]

lemma trivial_iff_size_le_one : size C ≤ 1 ↔ ¬ nontrivial C :=
by rw [← nontrivial_iff_one_lt_size, not_lt]

lemma nontrivial_iff_exists_distinct : nontrivial C ↔ ∃ x y ∈ C, x ≠ y := 
by simp_rw [← nontrivial_iff_one_lt_size, size, one_lt_card, finset_like.mem_coe]

lemma trivial_iff_forall_eq : ¬ nontrivial C ↔ ∀ x y ∈ C, x = y :=
by simp_rw [nontrivial_iff_exists_distinct, not_exists, not_not]

def min_dist (C : S) :=
if H : nontrivial C then (codewords C).off_diag.inf' H (function.uncurry hamming_dist) 
else 0

lemma min_dist_eq_zero_of_trivial (h : ¬ nontrivial C) : min_dist C = 0 := dif_neg h

lemma min_dist_ne_zero_of_nontrivial (h : nontrivial C) : min_dist C ≠ 0 := 
begin
  simp_rw [min_dist, dif_pos h, ← zero_lt_iff, lt_inf'_iff], rintros ⟨x, y⟩ hxy,
  rw [function.uncurry_apply_pair, hamming_dist_pos], rw mem_off_diag at hxy, exact hxy.2.2
end

@[simp] lemma min_dist_ne_zero_iff_nontrivial : ¬ min_dist C = 0 ↔ nontrivial C := 
⟨ λ h, by { contrapose! h, exact min_dist_eq_zero_of_trivial h }, min_dist_ne_zero_of_nontrivial⟩

lemma min_dist_eq_zero_iff_trivial :
  min_dist C = 0 ↔ ¬nontrivial C := min_dist_ne_zero_iff_nontrivial.not_right

lemma min_dist_eq_zero_iff_forall_dist_eq_zero :
  min_dist C = 0 ↔ ∀ x y ∈ C, hamming_dist x y = 0 :=
by { simp_rw [min_dist_eq_zero_iff_trivial, trivial_iff_forall_eq, hamming_dist_eq_zero], refl }

lemma min_dist_le_iff_exists_dist_le {d : ℕ} (hC : nontrivial C) : min_dist C ≤ d.succ ↔ 
  ∃ (x y ∈ C), x ≠ y ∧ hamming_dist x y ≤ d.succ :=
begin
  simp_rw [min_dist, dif_pos hC, inf'_le_iff, mem_off_diag, finset_like.mem_coe],
  exact ⟨ λ ⟨_, ⟨hx, hy, hxy⟩, hxyd⟩, ⟨_, hx, _, hy, hxy, hxyd⟩,
          λ ⟨_, hx, _, hy, hxy, hxyd⟩, ⟨⟨_, _⟩, ⟨hx, hy, hxy⟩, hxyd⟩ ⟩
end

lemma lt_min_dist_of_forall_lt_dist {d : ℕ} (hC : nontrivial C) : d < min_dist C ↔ 
  ∀ (x y ∈ C), x ≠ y → d < hamming_dist x y :=
begin
  simp_rw [min_dist, dif_pos hC, lt_inf'_iff, mem_off_diag, finset_like.mem_coe], 
  exact ⟨ λ H _ hx _ hy hxy, H ⟨_, _⟩ ⟨hx, hy, hxy⟩,
          λ H _ ⟨hx, hy, hxy⟩, H _ hx _ hy hxy ⟩
end

lemma min_dist_eq_succ_of_exists_eq_forall_lt_dist {d : ℕ} : 
  min_dist C = d.succ → (∃ x y ∈ C, x ≠ y ∧ hamming_dist x y = d.succ) ∧ 
  ∀ x y ∈ C, x ≠ y → d < hamming_dist x y :=
begin
  by_cases hC : nontrivial C,
  { simp_rw [ le_antisymm_iff, nat.succ_le_iff, lt_min_dist_of_forall_lt_dist hC,
              min_dist_le_iff_exists_dist_le hC],
    exact λ ⟨⟨_, hx, _, hy, hxy, hxyd⟩, H⟩, ⟨⟨_, hx, _, hy, hxy, hxyd, H _ hx _ hy hxy⟩, H⟩
  },
  { rw ← min_dist_eq_zero_iff_trivial at hC, intro H, rw H at hC, exact nat.no_confusion hC }
end

lemma exists_eq_forall_lt_dist_of_min_dist_eq_succ {d : ℕ} : 
( (∃ x y ∈ C, x ≠ y ∧ hamming_dist x y = d.succ) ∧ 
  ∀ x y ∈ C, x ≠ y → d < hamming_dist x y) → min_dist C = d.succ  :=
begin
  by_cases hC : nontrivial C,
  { simp_rw [ le_antisymm_iff, nat.succ_le_iff, lt_min_dist_of_forall_lt_dist hC,
              min_dist_le_iff_exists_dist_le hC], 
    exact λ ⟨⟨_, hx, _, hy, hxy, hxyd⟩, H⟩, ⟨⟨_, hx, _, hy, hxy, hxyd.1⟩, H⟩
  },
  { rw trivial_iff_forall_eq at hC, rintro ⟨⟨x, hx, y, hy, hxy, _⟩, _⟩,
    exact false.elim (hxy (hC x hx y hy)) }
end

lemma min_dist_eq_succ_iff_exists_eq_forall_lt_dist {d : ℕ} : 
  min_dist C = d.succ ↔ (∃ x y ∈ C, x ≠ y ∧ hamming_dist x y = d.succ) ∧ 
  ∀ x y ∈ C, x ≠ y → d < hamming_dist x y :=
⟨min_dist_eq_succ_of_exists_eq_forall_lt_dist, exists_eq_forall_lt_dist_of_min_dist_eq_succ⟩

end coding

structure block_code {ι : Type*} (β : ι → Type*) := (carrier : finset (hamming β))

namespace block_code

variables {ι : Type*} {β : ι → Type*} {c : hamming β}

instance : finset_like (block_code β) (hamming β) :=
⟨block_code.carrier, λ C D h, by { cases C, cases D, congr' }⟩

@[simp] lemma mem_carrier {C : block_code β} : c ∈ C.carrier ↔ c ∈ C := iff.rfl

@[ext] theorem ext {C C' : block_code β} (h : ∀ c, c ∈ C ↔ c ∈ C') : C = C' := set_like.ext h

instance : inhabited (block_code β) := ⟨⟨∅⟩⟩

def equiv_finset : block_code β ≃ finset (hamming β) := 
{ to_fun := coe,
  inv_fun := mk,
  left_inv := λ C, by { cases C, refl },
  right_inv := λ _, rfl }

variables [fintype ι] [Π i, decidable_eq (β i)] {C : block_code β}
open coding

#check codewords C

end block_code

#lint