import data.finset.card
import data.set_like.basic

@[protect_proj]
class finset_like (A : Type*) (B : out_param $ Type*) :=
(coe : A → finset B)
(coe_injective' : function.injective coe)

namespace finset_like

variables {A : Type*} {B : Type*} [i : finset_like A B]

include i

instance : has_coe_t A (finset B) := ⟨finset_like.coe⟩

theorem coe_injective : function.injective (coe : A → finset B) :=
λ x y h, finset_like.coe_injective' h

@[nolint dangerous_instance, priority 100]
instance to_set_like : set_like A B := 
{ coe := coe ∘ finset_like.coe,
  coe_injective' := finset.coe_injective.comp (finset_like.coe_injective) }

@[simp] lemma coe_coe {s : A} : ((s : finset B) : set B) = (s : set B) := rfl

variables (p q : A)

variables {p q}

@[simp, norm_cast] theorem coe_finset_eq : (p : finset B) = q ↔ p = q := coe_injective.eq_iff

theorem ext' (h : (p : finset B) = q) : p = q := coe_injective h

theorem ext'_iff : p = q ↔ (p : finset B) = q := coe_finset_eq.symm

@[simp] theorem mem_coe {x : B} : x ∈ (p : finset B) ↔ x ∈ p := iff.rfl

@[simp, norm_cast] lemma coe_subset_coe {S T : A} : (S : finset B) ⊆ T ↔ S ≤ T := iff.rfl

@[mono] lemma coe_mono : monotone (coe : A → finset B) := λ a b, coe_subset_coe.mpr

@[simp, norm_cast] lemma coe_ssubset_coe {S T : A} : (S : finset B) ⊂ T ↔ S < T := iff.rfl

@[mono] lemma coe_strict_mono : strict_mono (coe : A → finset B) := λ a b, coe_ssubset_coe.mpr

end finset_like