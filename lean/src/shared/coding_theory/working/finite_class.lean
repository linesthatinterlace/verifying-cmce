import data.set_like.basic
import data.set.finite

class finite_class (S : Type*) (M : out_param $ Type*) [set_like S M] :=
(finite : ∀ s : S, (s : set M).finite)

namespace finite_class
variables {S M : Type*} [set_like S M] [finite_class S M] {m : M} {s : S}

noncomputable instance : has_coe_t S (finset M) := ⟨λ s, (finite s).to_finset⟩

@[simp] lemma mem_coe : m ∈ (s : finset M) ↔ m ∈ s := set.finite.mem_to_finset (finite s)

@[simp] lemma coe_coe {s : S} : ((s : finset M) : set M) = (s : set M) := 
by { ext, rw [set_like.mem_coe, finset.mem_coe, mem_coe] }

noncomputable def card (s : S) := (s : finset M).card

end finite_class

structure finite_set (α : Type*) := 
(carrier : set α)
(finite' : carrier.finite)

namespace finite_set

section set_like_boilerplate
variables {α : Type*} {c : α}

instance : set_like (finite_set α) α :=
⟨finite_set.carrier, λ s D h, by { cases s, cases D, congr' }⟩

instance : finite_class (finite_set α) α := { finite := finite' }

@[simp] lemma mem_carrier {s : finite_set α} : c ∈ s.carrier ↔ c ∈ (s : set α) := iff.rfl

@[simp]
lemma mem_mk {S : set α} {x : α} (h) : x ∈ (⟨S, h⟩ : finite_set α) ↔ x ∈ S := iff.rfl

@[simp]
lemma coe_set_mk {S : set α} (h) : ((⟨S, h⟩ : finite_set α) : set α) = S := rfl

@[simp]
lemma mk_le_mk {S S' : set α} (h h') :
  (⟨S, h⟩ : finite_set α) ≤ (⟨S', h'⟩ : finite_set α) ↔ S ⊆ S' := iff.rfl

@[ext] theorem ext {s s' : finite_set α} (h : ∀ c, c ∈ s ↔ c ∈ s') : s = s' := set_like.ext h

/-- Copy of a `my_subobject` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (s : finite_set α) (s' : set α) (hs : s' = ↑s) : finite_set α :=
{ carrier := s',
  finite' := hs.symm ▸ s.finite' }

@[simp] lemma coe_copy (s : finite_set α) (s' : set α) (hs : s' = ↑s) :
  (s.copy s' hs : set α) = s' := rfl

lemma copy_eq (s : finite_set α) (s' : set α) (hs : s' = ↑s) : s.copy s' hs = s :=
set_like.coe_injective hs

end set_like_boilerplate

section finite_class_boilerplate
variables {α : Type*} {c : α}

lemma finite (s : finite_set α) : (s : set α).finite := finite_class.finite _

noncomputable def card (s : finite_set α) := finite_class.card s

lemma card_coe_eq_card (s : finite_set α) : (s : finset α).card = s.card := rfl

end finite_class_boilerplate

section substance
variables {α : Type*} {c : α}

instance : inhabited (finite_set α) := ⟨⟨∅, set.finite_empty⟩⟩

def of_finset (s : finset α) : finite_set α := ⟨s, s.finite_to_set⟩

noncomputable def equiv_finset : finite_set α ≃ finset α := 
{ to_fun := coe,
  inv_fun := of_finset,
  left_inv := λ C, by { cases C, simp_rw [of_finset, finite_class.coe_coe, coe_set_mk] },
  right_inv := finset.finite_to_set_to_finset }

lemma coe_inj : function.injective (coe : finite_set α → finset α) :=
function.left_inverse.injective equiv_finset.left_inv

lemma of_finset_inj : function.injective (of_finset : finset α → finite_set α) :=
function.left_inverse.injective equiv_finset.right_inv

@[simp] lemma of_finset_coe (s : finite_set α) : of_finset ↑s = s := equiv_finset.left_inv _

@[simp] lemma coe_of_finset (s : finset α) : ↑(of_finset s) = s := equiv_finset.right_inv _

lemma of_finset_card_eq_card (s : finset α) : (of_finset s).card = s.card := 
by rw [card, finite_class.card, coe_of_finset]

end substance

end finite_set
#lint