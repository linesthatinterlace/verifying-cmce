import topology.metric_space.basic
import analysis.normed.group.basic

namespace fintype
open subtype

variables {α : Type*} (p q : α → Prop)
[fintype {x // p x}] [fintype {x // q x}] [fintype {x // p x ∨ q x}] [fintype {x // p x ∧ q x}]

-- PR THIS

theorem card_subtype_le_of_imp (h : p ≤ q) : card {x // p x} ≤ card {x // q x} := card_le_of_embedding (imp_embedding _ _ h)

end fintype

open fintype

def ham {ι : Type*} [fintype ι] (β : ι → Type*) [Π i, decidable_eq (β i)] : Type* := Π i, β i

local notation `𝓗[` K`,` n`]` := ham (λ _ : fin n, K)

namespace hamming

variables {α ι : Type*} [semiring α] [fintype ι] {β : ι → Type*} [Π i, decidable_eq (β i)] 
@[pattern] def of_ham : ham β ≃ Π i, β i := equiv.refl _
@[pattern] def to_ham : (Π i, β i) ≃ ham β := equiv.refl _

@[simp] lemma to_ham_symm_eq : (@to_ham _ _ β _).symm = of_ham := rfl
@[simp] lemma of_ham_symm_eq : (@of_ham _ _ β _).symm = to_ham := rfl
@[simp] lemma to_ham_of_ham (x : ham β) : to_ham (of_ham x) = x := rfl
@[simp] lemma of_ham_to_ham (x : Π i, β i) : of_ham (to_ham x) = x := rfl
@[simp] lemma to_ham_inj {x y : Π i, β i} : to_ham x = to_ham y ↔ x = y := iff.rfl
@[simp] lemma of_ham_inj {x y : ham β} : of_ham x = of_ham y ↔ x = y := iff.rfl

instance [Π i, has_zero (β i)] : has_zero (ham β) := pi.has_zero
instance [Π i, has_add (β i)] : has_add (ham β) := pi.has_add
instance [Π i, has_sub (β i)] : has_sub (ham β) := pi.has_sub
instance [Π i, has_mul (β i)] : has_mul (ham β) := pi.has_mul
instance [Π i, has_div (β i)] : has_div (ham β) := pi.has_div
instance [Π i, add_group (β i)] : add_group (ham β) := pi.add_group
instance [Π i, add_comm_group (β i)] : add_comm_group (ham β) := pi.add_comm_group
instance [Π i, add_comm_monoid (β i)] : add_comm_monoid (ham β) := pi.add_comm_monoid

instance [Π i, add_comm_monoid (β i)] [Π i, module α (β i)] : module α (ham β) := pi.module _ _ _

def ham_dist (x y : ham β) := card {i // x i ≠ y i}

instance : has_dist (ham β) := ⟨λ x y, ham_dist x y⟩

@[simp, push_cast] lemma dist_eq_ham_dist (x y : ham β) : dist x y = ham_dist x y := rfl

lemma ham_dist_eq (x y : ham β) : ham_dist x y = card {i // x i ≠ y i} := rfl

@[simp] lemma ham_dist_self (x : ham β) : ham_dist x x = 0 := 
by simp [ham_dist_eq, card_eq_zero_iff]; apply_instance

lemma ham_dist_comm (x y : ham β) : ham_dist x y = ham_dist y x := 
by simp_rw [ham_dist_eq, ne_comm]

lemma ham_dist_triangle (x y z : ham β) : ham_dist x z ≤ ham_dist x y + ham_dist y z :=
begin
  simp_rw ham_dist_eq, refine le_trans (card_subtype_le_of_imp _ _ (λ _ h, _))
  (card_subtype_or _ _), contrapose! h, exact h.1.symm ▸ h.2
end

lemma eq_of_ham_dist_eq_zero (x y : ham β) (h : ham_dist x y = 0) : x = y :=
begin
  contrapose h, rw [←ne.def, function.ne_iff] at h, rcases h with ⟨i, hi⟩,
  rw [ham_dist_eq, card_eq_zero_iff], exact λ H, H.elim' ⟨i, hi⟩
end

lemma ham_dist_eq_zero (x y : ham β) : ham_dist x y = 0 ↔ x = y :=
⟨eq_of_ham_dist_eq_zero x y, λ h, h ▸ ham_dist_self _⟩

lemma ham_dist_pos (x y : ham β) : 0 < ham_dist x y ↔ x ≠ y :=
by rw [ne.def, ← ham_dist_eq_zero, decidable.iff_not_comm, not_lt, le_zero_iff]
 
instance : metric_space (ham β) := 
{ dist_self           := by push_cast; exact_mod_cast ham_dist_self,
  dist_comm           := by push_cast; exact_mod_cast ham_dist_comm,
  dist_triangle       := by push_cast; exact_mod_cast ham_dist_triangle,
  eq_of_dist_eq_zero  := by push_cast; exact_mod_cast eq_of_ham_dist_eq_zero }

section has_zero

variables [Π i, has_zero (β i)]

def ham_weight (x : ham β) : ℕ := ham_dist x 0

instance : has_norm (ham β) := ⟨λ x, ham_weight x⟩

@[simp, push_cast] lemma norm_eq_ham_weight (x : ham β) : ∥x∥ = ham_weight x := rfl

lemma ham_weight_eq (x : ham β) : ham_weight x = card {i // x i ≠ 0} := rfl

@[simp] lemma ham_weight_zero_eq_zero : ham_weight (0 : ham β) = 0 := 
ham_dist_self _

lemma zero_of_ham_weight_eq_zero (x : ham β) (h : ham_weight x = 0) : x = 0 := 
eq_of_ham_dist_eq_zero _ _ h

lemma ham_weight_eq_zero_iff_zero (x : ham β) : ham_weight x = 0 ↔ x = 0 := 
ham_dist_eq_zero _ _

lemma ham_weight_pos_iff_neq (x : ham β) : 0 < ham_weight x ↔ x ≠ 0 := 
ham_dist_pos _ _

end has_zero

lemma ham_dist_eq_ham_weight_sub [Π i, add_group (β i)] (x y : ham β) : 
ham_dist x y = ham_weight (x - y) :=
by simp_rw [ham_dist_eq, ham_weight_eq, pi.sub_apply, sub_ne_zero]

instance [Π i, add_comm_group (β i)] : normed_group (ham β) := 
{ dist_eq := by push_cast; exact_mod_cast ham_dist_eq_ham_weight_sub }

end hamming