import data.finset.basic

@[protect_proj]
class finset_like (A : Type*) (B : out_param $ Type*) :=
(coe : A → finset B)
(coe_injective' : function.injective coe)

namespace finset_like

variables {A : Type*} {B : Type*} [i : finset_like A B]

include i

instance : has_coe_t A (finset B) := ⟨finset_like.coe⟩

@[priority 100]
instance : has_mem B A := ⟨λ x p, x ∈ (p : finset B)⟩

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance, priority 100]
instance : has_coe_to_sort A Type* := ⟨λ p, {x : B // x ∈ p}⟩

variables (p q : A)

@[simp, norm_cast] theorem coe_sort_coe : ((p : finset B) : Type*) = p := rfl

variables {p q}

theorem coe_injective : function.injective (coe : A → finset B) :=
λ x y h, finset_like.coe_injective' h

@[simp, norm_cast] theorem coe_set_eq : (p : finset B) = q ↔ p = q := coe_injective.eq_iff

theorem ext' (h : (p : finset B) = q) : p = q := coe_injective h

theorem ext'_iff : p = q ↔ (p : finset B) = q := coe_set_eq.symm

/-- Note: implementers of `finset_like` must copy this lemma in order to tag it with `@[ext]`. -/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := coe_injective $ finset.ext h

theorem ext_iff : p = q ↔ (∀ x, x ∈ p ↔ x ∈ q) := coe_injective.eq_iff.symm.trans finset.ext_iff

@[simp] theorem mem_coe {x : B} : x ∈ (p : finset B) ↔ x ∈ p := iff.rfl

@[simp, norm_cast] lemma coe_eq_coe {x y : p} : (x : B) = y ↔ x = y := subtype.ext_iff_val.symm

@[simp, norm_cast] lemma coe_mk (x : B) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : B) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : B) ∈ p := x.2

@[simp] protected lemma eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x := subtype.eta x hx

-- `dangerous_instance` does not know that `B` is used only as an `out_param`
@[nolint dangerous_instance, priority 100]
instance : partial_order A :=
{ le := λ H K, ∀ ⦃x⦄, x ∈ H → x ∈ K,
  .. partial_order.lift (coe : A → finset B) coe_injective }

lemma le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T := iff.rfl

@[simp, norm_cast]
lemma coe_subset_coe {S T : A} : (S : finset B) ⊆ T ↔ S ≤ T := iff.rfl

@[mono] lemma coe_mono : monotone (coe : A → finset B) := λ a b, coe_subset_coe.mpr

@[simp, norm_cast]
lemma coe_ssubset_coe {S T : A} : (S : finset B) ⊂ T ↔ S < T := iff.rfl

@[mono] lemma coe_strict_mono : strict_mono (coe : A → finset B) := λ a b, coe_ssubset_coe.mpr

lemma not_le_iff_exists : ¬(p ≤ q) ↔ ∃ x ∈ p, x ∉ q := finset.not_subset _ _

lemma exists_of_lt : p < q → ∃ x ∈ q, x ∉ p := finset.exists_of_ssubset

lemma lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p :=
by rw [lt_iff_le_not_le, not_le_iff_exists]

end finset_like