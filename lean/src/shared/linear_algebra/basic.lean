import linear_algebra.span

namespace linear_map
open submodule

variables {R : Type*} {R₂ : Type*} [semiring R] [semiring R₂] {M : Type*} {M₂ : Type*}
{τ₁₂ : R →+* R₂}

section comap

variables [add_comm_monoid M] [module R M] [add_comm_monoid M₂] [module R₂ M₂]
(f : M →ₛₗ[τ₁₂] M₂) {p p' : submodule R M} {q q' : submodule R₂ M₂} 

lemma ker_eq_comap : f.ker = comap f ⊥ := rfl

lemma ker_le_comap {f : M →ₛₗ[τ₁₂] M₂} : f.ker ≤ comap f q := comap_mono bot_le

section ring_hom_surjective

variable [ring_hom_surjective τ₁₂]

-- This should not be primed (to match the map equivalent).

lemma comap_le_comap_iff' : comap f q ≤ comap f q' ↔ f.range ⊓ q ≤ q' := 
by rw [← map_le_iff_le_comap, map_comap_eq]

lemma comap_range : comap f (f.range) = ⊤ := submodule.eq_top_iff'.mpr (λ _, ⟨_, rfl⟩)

lemma comap_eq_comap_range_inf : comap f q = comap f (f.range ⊓ q) :=
by rw [comap_inf, comap_range, top_inf_eq]

lemma comap_le_ker_iff : comap f q ≤ f.ker ↔ f.range ⊓ q = ⊥ :=
by rw [ker_eq_comap, comap_le_comap_iff', le_bot_iff]

lemma comap_eq_ker_iff : comap f q = f.ker ↔ f.range ⊓ q = ⊥ :=
⟨ λ h, (comap_le_ker_iff _).mp (le_of_eq h),
  λ h, le_antisymm ((comap_le_ker_iff _).mpr h) ker_le_comap⟩

end ring_hom_surjective

-- comap_map_eq and comap_map_eq_self are in the wrong file (should be in basic).

end comap

section map
variables [ring_hom_surjective τ₁₂]
section monoids

variables [add_comm_monoid M] [module R M] [add_comm_monoid M₂] [module R₂ M₂]
(f : M →ₛₗ[τ₁₂] M₂) {p p' : submodule R M} {q q' : submodule R₂ M₂}

lemma map_ker : map f (f.ker) = ⊥ := (submodule.eq_bot_iff _).mpr
(λ x h, by rcases (mem_map.mp h) with ⟨_, p, l⟩; exact l ▸ (mem_ker.mp p) )

lemma map_eq_map_sup_ker : map f p = map f (p ⊔ f.ker) :=
by rw [map_sup, map_ker, sup_bot_eq]

end monoids

section group
variables [add_comm_group M] [module R M] [add_comm_group M₂] [module R₂ M₂]
(f : M →ₛₗ[τ₁₂] M₂) {p p' : submodule R M} {q q' : submodule R₂ M₂}

lemma range_le_map_iff : f.range ≤ map f p ↔ p ⊔ f.ker = ⊤ :=
by rw [range_eq_map, linear_map.map_le_map_iff, top_le_iff]

-- map_eq_top_iff is just a special case of this.
lemma range_eq_map_iff : f.range = map f p ↔ p ⊔ f.ker = ⊤ :=
⟨ λ h, (range_le_map_iff _).mp (le_of_eq h),
  λ h, le_antisymm ((range_le_map_iff _).mpr h) map_le_range⟩
end group

-- map_le_map_iff and map_le_map_iff' should be in basic also.

end map

section cmptble
variables 
[add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module R₂ M₂] 
{f : M →ₛₗ[τ₁₂] M₂} (p p' : submodule R M) (q q' : submodule R₂ M₂) 

def compatible (f : M →ₛₗ[τ₁₂] M₂) (p) (q) : Prop := p ≤ comap f q

lemma cmptble_def {p q} : f.compatible p q ↔ p ≤ comap f q := by refl

lemma cmptble_comap : f.compatible (comap f q) q := le_refl _

lemma cmptble_bot_ker : f.compatible f.ker ⊥ := le_refl _

lemma cmptble_of_cmptble_of_dom_le {p p' q}
(hp : p' ≤ p) (hf : f.compatible p q) : f.compatible p' q := λ _ hx, hf (hp hx)

lemma cmptble_of_cmptble_of_cod_le {p q q'}
(hq : q ≤ q') (hf : f.compatible p q) : f.compatible p q' := λ _ hx, hq (hf hx)

lemma cmptble_of_cmptble_of_dom_le_of_cod_le {p q p' q'}
(hp : p' ≤ p) (hq : q ≤ q') (hf : f.compatible p q) : f.compatible p' q' := 
cmptble_of_cmptble_of_cod_le hq (cmptble_of_cmptble_of_dom_le hp hf)

lemma cmptble_dom_cod_top : f.compatible ⊤ ⊤ := 
cmptble_of_cmptble_of_dom_le (le_refl _) (cmptble_comap ⊤)

lemma cmptble_cod_top {p} : f.compatible p ⊤ :=
cmptble_of_cmptble_of_dom_le le_top cmptble_dom_cod_top 

lemma cmptble_cod_bot_iff {p} : f.compatible p ⊥ ↔ p ≤ f.ker :=
by rw cmptble_def; refl

section ring_hom_surjective
variables [ring_hom_surjective τ₁₂]

lemma cmptble_def' {p q} : f.compatible p q ↔ map f p ≤ q := 
(gc_map_comap _ _ _).symm

lemma cmptble_map : f.compatible p (map f p) :=
cmptble_def'.mpr (le_refl _)

lemma cmptble_top_range : f.compatible ⊤ f.range := 
by rw ←map_top; exact cmptble_of_cmptble_of_cod_le (le_refl _) (cmptble_map ⊤)

lemma cmptble_dom_top_iff {q} : f.compatible ⊤ q ↔ f.range ≤ q :=
by rw [cmptble_def', map_top f]

end ring_hom_surjective

lemma cmptble_iff_map_mem_of_mem {p q}: f.compatible p q ↔ ∀ x, x ∈ p → f x ∈ q := by refl

lemma cmptble_dom_top_iff' {q} : f.compatible ⊤ q ↔ ∀ x, f x ∈ q :=
⟨λ h _, h mem_top, λ h x _, h x⟩

lemma cmptble_cod_bot_iff' {p} : f.compatible p ⊥ ↔ ∀ x ∈ p, f x = 0 :=
by rw cmptble_cod_bot_iff; refl

-- Should be equivalent to the existing restrict.
def restrict' (f : M →ₛₗ[τ₁₂] M₂) {p} {q} (hf : f.compatible p q) : p →ₛₗ[τ₁₂] q := { 
  to_fun := λ x, ⟨f x, hf x.2⟩,
  map_add' := by { simp_rw [  subtype.ext_iff, submodule.coe_add,
                              map_add, submodule.coe_mk], exact λ _ _, rfl},
  map_smul' := by { simp_rw [ subtype.ext_iff, submodule.coe_smul,
                              map_smulₛₗ, submodule.coe_mk], exact λ _ _, rfl} }

lemma restrict'_apply {p} {q} {hf : f.compatible p q} {x} : (f.restrict' hf x : M₂) = f x := rfl

-- Should be equivalent to the existing dom_restrict.
-- Suggestion: linear version should be ldom_restrict? etc.

def dom_restrict'' (f : M →ₛₗ[τ₁₂] M₂) (p : submodule R M) : p →ₛₗ[τ₁₂] M₂ := 
top_equiv.to_linear_map.comp (f.restrict' cmptble_cod_top)

lemma dom_restrict''_apply {f : M →ₛₗ[τ₁₂] M₂} {p} {x} : f.dom_restrict'' p x = f x := rfl

lemma dom_restrict''_cmptble_top_of_cmptble {p q} (hf : f.compatible p q) :
(f.dom_restrict'' p).compatible ⊤ q :=
by rw cmptble_dom_top_iff'; exact λ x, hf x.2

def cod_restrict' (f : M →ₛₗ[τ₁₂] M₂) {q} (hf : f.compatible ⊤ q) : M →ₛₗ[τ₁₂] q := 
(f.restrict' hf).comp top_equiv.symm.to_linear_map

lemma cod_restrict'_apply {q} {hq : f.compatible ⊤ q} {x} : (f.cod_restrict' hq x : M₂) = f x := 
rfl

lemma restrict'_eq_cod_restrict_dom_restrict' {p q} {hf : f.compatible p q} :
f.restrict' hf = (f.dom_restrict'' p).cod_restrict' (dom_restrict''_cmptble_top_of_cmptble hf) := 
rfl

lemma restrict'_eq_dom_restrict_cod_restrict' {p q} {hf : f.compatible ⊤ q} :
f.restrict' (cmptble_of_cmptble_of_dom_le le_top hf) = (f.cod_restrict' hf).dom_restrict'' p := 
rfl

end cmptble

-- To add:
/-
(_ ⧸ (p ⊓ f.ker).comap p.subtype) ≃ₗ[R] p.map f
rank f.range ⊔ q + rank q.comap f = rank M + rank q
(?) corank q = corank q.comap f + corank (f.range ⊔ q)

Should link "compatible" with the corresponding stuff in the quotient space.

-/

end linear_map