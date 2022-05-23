import linear_algebra.span

namespace submodule

variables {R : Type*} [semiring R]
variables {M : Type*} [add_comm_monoid M] [module R M] {p p' : submodule R M} 

def comap_subtype_equiv_inf_right :
comap p.subtype p' ≃ₗ[R] (p ⊓ p' : submodule R M) :=
{ to_fun := λ ⟨⟨_, hx⟩, hx'⟩, ⟨_, ⟨hx, hx'⟩⟩,
  inv_fun := λ ⟨_, ⟨hx, hx'⟩⟩, ⟨⟨_, hx⟩, hx'⟩,
  left_inv := λ ⟨⟨_, _⟩, _⟩, rfl,
  right_inv := λ ⟨_, ⟨_, _⟩⟩, rfl,
  map_add' := λ ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩, rfl,
  map_smul' := λ _ ⟨⟨_, _⟩, _⟩, rfl
}

def comap_subtype_equiv_inf_left :
comap p.subtype p' ≃ₗ[R] (p' ⊓ p : submodule R M) := 
linear_equiv.trans comap_subtype_equiv_inf_right (linear_equiv.of_eq _ _ inf_comm)

variables {M₂ : Type*} [add_comm_monoid M₂] [module R M₂] {q : submodule R M₂}

def prod_equiv : p.prod q ≃ₗ[R] p × q :=
{ map_add' := λ x y, rfl, map_smul' := λ x y, rfl, .. equiv.set.prod ↑p ↑q }

end submodule