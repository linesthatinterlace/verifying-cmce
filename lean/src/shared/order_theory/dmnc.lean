import tactic

section dmnc
section set
variables {α : Type*} {s t : set α} [preorder α] 

/- Define the set of lower cuts. -/

def lcuts (α : Type*) [preorder α] : set (set α) := 
{s | lower_bounds (upper_bounds s) ≤ s}

lemma mem_lcuts_iff_eq : s ∈ lcuts α ↔ 
lower_bounds (upper_bounds s) = s := 
⟨λ H, set.eq_of_subset_of_subset H (subset_lower_bounds_upper_bounds _), 
λ H, le_of_eq H⟩

lemma inf_lcuts_mem_lcuts (hs : s ∈ lcuts α) (ht : t ∈ lcuts α) :
s ⊓ t ∈ lcuts α :=
λ _ ha, ⟨hs (λ _ hb, ha (λ _ ⟨hc, _⟩, hb hc)), ht (λ _ hb, ha (λ _ ⟨_, hc⟩, hb hc))⟩

lemma Inf_lcuts_mem_lcuts {S : set (set α)} (hS : S ≤ lcuts α) :
⋂₀ S ∈ lcuts α :=
begin
  intros _ ha _ ht, rw [← mem_lcuts_iff_eq.mp (hS ht)],
  exact λ _ hb, ha (λ _ hc, hb (hc _ ht))
end

lemma sInter_lcuts_mem_lcuts : ⋂₀ lcuts α ∈ lcuts α :=
Inf_lcuts_mem_lcuts (le_refl _)

lemma Iic_mem_lcuts (a : α) : set.Iic a ∈ lcuts α := λ _ hb, hb (λ _ hc, hc)

/- Define the set of upper cuts. -/

def ucuts (α : Type*) [preorder α] : set (set α) := 
{s | upper_bounds (lower_bounds s) ≤ s}

lemma mem_ucuts_iff_eq : s ∈ ucuts α ↔ 
upper_bounds (lower_bounds s) = s :=
⟨λ H, set.eq_of_subset_of_subset H (subset_upper_bounds_lower_bounds _),
λ H, le_of_eq H⟩

lemma inf_ucuts_mem_ucuts (hs : s ∈ ucuts α) (ht : t ∈ ucuts α) :
s ⊓ t ∈ ucuts α :=
λ _ ha, ⟨hs (λ _ hb, ha (λ _ ⟨hc, _⟩, hb hc)), ht (λ _ hb, ha (λ _ ⟨_, hc⟩, hb hc))⟩

lemma Inf_ucuts_mem_ucuts {S : set (set α)} (hS : S ≤ ucuts α) :
⋂₀ S ∈ ucuts α :=
begin
  intros _ ha _ ht, rw [← mem_ucuts_iff_eq.mp (hS ht)],
  exact λ _ hb, ha (λ _ hc, hb (hc _ ht))
end

lemma sInter_ucuts_mem_ucuts : ⋂₀ ucuts α ∈ ucuts α :=
Inf_ucuts_mem_ucuts (le_refl _)

/- And this is how they interact. -/
lemma ub_mem_ucuts_of_mem_lcuts {s : set α} (H : s ∈ lcuts α) : 
upper_bounds s ∈ ucuts α :=
by { rw mem_lcuts_iff_eq at H, rw [mem_ucuts_iff_eq, H] }

lemma lb_mem_lcuts_of_mem_ucuts {s : set α} (H : s ∈ ucuts α) : 
lower_bounds s ∈ lcuts α :=
by { rw mem_ucuts_iff_eq at H, rw [mem_lcuts_iff_eq, H] }

end set

/- Initially define in terms of the lower cut. We don't use this directly,
and try to maintain symmetry. -/

structure dmnc (α : Type*) [preorder α] :=
  (lcut' : set α)
  (cut_up' : lcut' ∈ lcuts α)

namespace dmnc
variables {α : Type*} {a b : α} {s t : set α}

section preorder
variables [preorder α] (A B : dmnc α) (X : set (dmnc α))

/- Define symmetric cuts. -/

/- Lower cuts -/
def lcut : set α := A.lcut'

lemma lcut_mem : A.lcut ∈ lcuts α := A.cut_up'

@[simp]
lemma lcut_eq : lower_bounds (upper_bounds (A.lcut)) = A.lcut :=
mem_lcuts_iff_eq.mp A.lcut_mem

def lcuts_set := lcut '' X

lemma lcuts_set_le_lcuts : lcuts_set X ≤ lcuts α := (λ s ⟨_, _, H⟩, H ▸ lcut_mem _)

lemma mem_lcuts_set : s ∈ lcuts_set X ↔ ∃ A ∈ X, (lcut A = s) :=
by simp_rw [lcuts_set, exists_prop]; refl

/- Upper cuts -/
def ucut : set α := upper_bounds A.lcut

@[simp]
lemma ucut_eq : upper_bounds (lower_bounds (A.ucut)) = A.ucut :=
by rw [ucut, lcut_eq]

lemma ucut_mem : A.ucut ∈ ucuts α := 
mem_ucuts_iff_eq.mpr A.ucut_eq

def ucuts_set := ucut '' X

lemma ucuts_set_le_ucuts : ucuts_set X ≤ ucuts α :=
(λ s ⟨_, _, H⟩, H ▸ ucut_mem _)

lemma mem_ucuts_set : s ∈ ucuts_set X ↔ ∃ A ∈ X, (ucut A = s) :=
by simp_rw [ucuts_set, exists_prop]; refl

/- This essentially shows the galois isomorphism. -/

lemma ucut_eq_ub_lcut : A.ucut = upper_bounds A.lcut := rfl

lemma lcut_eq_lb_ucut : A.lcut = lower_bounds A.ucut :=
by rw [ucut_eq_ub_lcut, lcut_eq]

/-
Relating order in sets between lcut and ucut.
-/

lemma le_lcut_of_ucut_le {A B : dmnc α} (H : B.ucut ≤ A.ucut): A.lcut ≤ B.lcut :=
by simp_rw [lcut_eq_lb_ucut]; exact λ _ ha, lower_bounds_mono_set H ha

lemma ucut_le_of_le_lcut {A B : dmnc α} (H : A.lcut ≤ B.lcut) : B.ucut ≤ A.ucut :=
by simp_rw [ucut_eq_ub_lcut]; exact λ _ ha, upper_bounds_mono_set H ha

lemma le_lcut_iff_ucut_le {A B : dmnc α} : A.lcut ≤ B.lcut ↔ B.ucut ≤ A.ucut :=
⟨λ H, ucut_le_of_le_lcut H, λ H, le_lcut_of_ucut_le H⟩

lemma lt_lcut_iff_ucut_lt {A B : dmnc α} : A.lcut < B.lcut ↔ B.ucut < A.ucut :=
by simp_rw [lt_iff_le_not_le, le_lcut_iff_ucut_le]

/-
Equality lemmas. One could have an ext here, but there are two exts you can take.
-/

lemma lcut_eq_iff_ucut_eq {A B : dmnc α} : A.lcut = B.lcut ↔ A.ucut = B.ucut :=
⟨λ H, set.eq_of_subset_of_subset
      (ucut_le_of_le_lcut (le_of_eq H.symm)) 
      (ucut_le_of_le_lcut (le_of_eq H)), 
λ H, set.eq_of_subset_of_subset
      (le_lcut_of_ucut_le (le_of_eq H.symm)) 
      (le_lcut_of_ucut_le (le_of_eq H)) ⟩

lemma eq_iff_lcut_eq {A B : dmnc α} : A = B ↔ A.lcut = B.lcut :=
by cases A; cases B; simp [lcut]

lemma eq_iff_ucut_eq {A B : dmnc α} : A = B ↔ A.ucut = B.ucut :=
by rw [eq_iff_lcut_eq, lcut_eq_iff_ucut_eq]

/- We can now clearly talk about sets in dmnc α in terms of lcuts or ucuts. -/
lemma mem_set_iff_lcut_mem_lcuts_set {A : dmnc α} {X : set (dmnc α)} :
A ∈ X ↔ A.lcut ∈ lcuts_set X :=
by {simp_rw [mem_lcuts_set, ← eq_iff_lcut_eq, exists_prop, exists_eq_right]}

lemma mem_set_iff_ucut_mem_ucuts_set {A : dmnc α} {X : set (dmnc α)} : 
A ∈ X ↔ A.ucut ∈ ucuts_set X :=
by simp_rw [mem_ucuts_set, ← eq_iff_ucut_eq, exists_prop, exists_eq_right]

/- Symmetric constructors for dmnc.  -/
def mk_lower {s : set α} (H : s ∈ lcuts α) : dmnc α := dmnc.mk s H

lemma mk_lower_lcut {s : set α} (H : s ∈ lcuts α) : (mk_lower H).lcut = s := rfl
lemma mk_lower_ucut {s : set α} (H : s ∈ lcuts α) : (mk_lower H).ucut = 
(upper_bounds s) := rfl

def mk_upper {t : set α} (H : t ∈ ucuts α) : dmnc α
:= dmnc.mk (lower_bounds t) (lb_mem_lcuts_of_mem_ucuts H)

lemma mk_upper_lcut {s : set α} (H : s ∈ ucuts α) : (mk_upper H).lcut = 
(lower_bounds s) := rfl

lemma mk_upper_ucut {s : set α} (H : s ∈ ucuts α) : (mk_upper H).ucut = s := 
by rwa [ucut_eq_ub_lcut, mk_upper_lcut, ← mem_ucuts_iff_eq]

/- Define notational instances. -/

instance : has_le (dmnc α) := ⟨λ A B, A.lcut ≤ B.lcut⟩

instance : has_Inf (dmnc α) :=
⟨λ X, mk_lower (Inf_lcuts_mem_lcuts (lcuts_set_le_lcuts X))⟩

instance : has_inf (dmnc α) := 
⟨λ A B, mk_lower (inf_lcuts_mem_lcuts A.lcut_mem B.lcut_mem)⟩

instance : has_Sup (dmnc α) :=
⟨λ X, mk_upper (Inf_ucuts_mem_ucuts (ucuts_set_le_ucuts X))⟩

instance : has_bot (dmnc α) := ⟨mk_lower sInter_lcuts_mem_lcuts⟩

instance : has_sup (dmnc α) := 
⟨λ A B, mk_upper (inf_ucuts_mem_ucuts A.ucut_mem B.ucut_mem)⟩

instance : has_top (dmnc α) := ⟨mk_upper (sInter_ucuts_mem_ucuts)⟩

/- Prove definitional lemmas about instances. -/

lemma le_iff_lcut_le {A B : dmnc α} : A ≤ B ↔ A.lcut ≤ B.lcut := by refl

lemma le_iff_ucut_le {A B : dmnc α} : A ≤ B ↔ B.ucut ≤ A.ucut :=
by rw [le_iff_lcut_le, le_lcut_iff_ucut_le]

lemma Inf_lcut : (Inf X).lcut = ⋂₀ (lcuts_set X) := rfl

lemma inf_lcut : (A ⊓ B).lcut = A.lcut ⊓ B.lcut := rfl

lemma bot_lcut : (⊥ : dmnc α).lcut = ⋂₀ (lcuts α) := rfl

lemma Sup_ucut : (Sup X).ucut = ⋂₀ (ucuts_set X) := mk_upper_ucut _

lemma sup_ucut : (A ⊔ B).ucut = A.ucut ⊓ B.ucut := mk_upper_ucut _

lemma top_ucut : (⊤ : dmnc α).ucut = ⋂₀ (ucuts α) := mk_upper_ucut _

/- The Dedekind-MacNeille construction is a complete lattice. -/

instance : complete_lattice (dmnc α) :=
{ le := (≤),
  le_refl := λ a,         by  rw le_iff_lcut_le; exact le_refl _,
  le_trans := λ a b c,    by  simp_rw le_iff_lcut_le; exact subset_trans,
  le_antisymm := λ a b,   by  simp_rw [le_iff_lcut_le, eq_iff_lcut_eq];
                              exact subset_antisymm,
  Inf := Inf,
  Inf_le := λ _ _ hA,     by  rw [le_iff_lcut_le];
                              exact set.sInter_subset_of_mem
                              (mem_set_iff_lcut_mem_lcuts_set.mp hA),
  le_Inf := λ _ _ ha,     by  rw [le_iff_lcut_le];
                              rintros _ hA _ ⟨_, hB, hs⟩;
                              exact hs ▸ le_iff_lcut_le.mp (ha _ hB) hA,
  inf := (⊓),
  inf_le_left := λ _ _,   by  rw [le_iff_lcut_le]; exact inf_le_left,
  inf_le_right := λ _ _,  by  rw [le_iff_lcut_le]; exact inf_le_right,
  le_inf := λ _ _ _,      by  simp_rw [le_iff_lcut_le]; exact le_inf,
  bot := ⊥,
  bot_le := λ _,          by  rw [le_iff_lcut_le]; 
                              exact set.sInter_subset_of_mem (lcut_mem _),
  Sup := Sup,
  le_Sup := λ _ _ hA,     by  rw [le_iff_ucut_le, Sup_ucut];
                              exact set.sInter_subset_of_mem
                              (mem_set_iff_ucut_mem_ucuts_set.mp hA),
  Sup_le := λ j u ha, by      rw [le_iff_ucut_le, Sup_ucut];
                              rintros _ hA _ ⟨_, hB, hs⟩;
                              exact hs ▸ le_iff_ucut_le.mp (ha _ hB) hA,
  sup := (⊔),
  le_sup_left := λ _ _,   by  rw [le_iff_ucut_le, sup_ucut]; exact inf_le_left,
  le_sup_right := λ _ _,  by  rw [le_iff_ucut_le, sup_ucut]; exact inf_le_right,
  sup_le := λ _ _ _,      by  simp_rw [le_iff_ucut_le, sup_ucut]; exact le_inf,
  top := ⊤,
  le_top := λ _,          by  rw [le_iff_ucut_le, top_ucut]; 
                              exact set.sInter_subset_of_mem (ucut_mem _) }

/- And it nearly preserves the original preorder. -/

def dmnc_map : α → dmnc α := λ x, mk_lower (Iic_mem_lcuts x)

lemma dmnc_map_lcut : (dmnc_map a).lcut = set.Iic a := rfl

lemma dmnc_map_ucut : (dmnc_map a).ucut = set.Ici a := 
by rw [ucut_eq_ub_lcut, dmnc_map_lcut, upper_bounds_Iic]

-- This must have some technical name, but, essentially, it preserves the
-- preorder "up to isomorphism".

lemma dmnc_map_order_preserving : dmnc_map a ≤ dmnc_map b ↔ a ≤ b :=
⟨λ H, H (le_refl _), λ H _ hc, le_trans hc H⟩

lemma dmnc_map_near_inj : dmnc_map a = dmnc_map b → a ≤ b ∧ b ≤ a :=
begin
  simp_rw [eq_iff_lcut_eq],
  intros hab, rw set.ext_iff at hab,
  exact ⟨(hab a).mp (le_refl _), (hab b).mpr (le_refl _)⟩,
end

def dmnc_map_order_hom : α →o dmnc α := 
{ to_fun := dmnc_map,
  monotone' := λ _ _, dmnc_map_order_preserving.mpr }

end preorder

section partial_order
variables [partial_order α]

-- In a partial order, we can go further - it's an order embedding.

lemma dmnc_map_injection : function.injective (dmnc_map : α → dmnc α) :=
begin
  simp_rw [function.injective],
  intros a b hab, rcases dmnc_map_near_inj hab with ⟨hab, hba⟩,
  exact le_antisymm hab hba
end

def dmnc_map_order_embedding : α ↪o dmnc α := 
{ to_fun := dmnc_map,
  inj' := dmnc_map_injection,
  map_rel_iff' := λ _ _, dmnc_map_order_preserving }

variables {β : Type*} [complete_lattice β]

-- In a precise sense, dmnc is the "smallest" complete lattice into which α
-- embeds (and probably that is true in some sense for preorders, but it isn't an
-- embedding there).

end partial_order

end dmnc
end dmnc