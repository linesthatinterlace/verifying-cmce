import tactic
import data.list.join

universes u v

variables {α : Type u} {β : Type v}

def code (α : Type u) (β : Type v) := α → list β

namespace code
open function list nat

variables (c : code α β)

def encoding : list α → list β := λ a, a.bind c

lemma encoding_eq (as : list α) : c.encoding as = as.bind c := rfl

lemma encoding_eq_nil (as : list α) : c.encoding as = nil ↔ ∀ a ∈ as, (c a) = nil := 
by { rw encoding_eq, exact bind_eq_nil }

@[simp]
lemma encoding_nil : c.encoding nil = nil := rfl

@[simp]
lemma encoding_cons (a) (as) : c.encoding (a :: as) = c a ++ c.encoding as := rfl

def decodable : Prop := injective (c.encoding)

lemma not_decodable_iff_exists_encodings_eq :
¬ c.decodable ↔ ∃ as as', c.encoding as = c.encoding as' ∧ as ≠ as' :=
by { unfold decodable injective, push_neg }

def len_fixed : Prop := ∀ a b, (c a).length = (c b).length

def fixed_len (n : ℕ) : Prop := ∀ a, (c a).length = n

lemma len_fixed_of_fixed_len {n : ℕ} (h : c.fixed_len n) : c.len_fixed := λ a b, by rw [h a, h b]

lemma exists_fixed_len_of_len_fixed [inhabited α] (h : c.len_fixed) : ∃ n, c.fixed_len n :=
⟨(c default).length, λ _, h _ _⟩

lemma len_fixed_iff_exists_fixed_len [inhabited α] : c.len_fixed ↔ ∃ n, c.fixed_len n :=
⟨exists_fixed_len_of_len_fixed _, λ ⟨_, h⟩, c.len_fixed_of_fixed_len h⟩

lemma len_encoding_eq_of_fixed_len {n : ℕ} (h : c.fixed_len n) (as)
: (c.encoding as).length = n * as.length :=
begin
  induction as with a as IH,
  { exact rfl }, 
  { simp only [IH, h a, mul_add, add_comm, length, encoding_cons, length_append, mul_one] }
end

lemma code_nil_of_fixed_len_zero (h : c.fixed_len 0) : ∀ a, (c a) = nil := 
λ _, eq_nil_of_length_eq_zero (h _)

lemma encoding_nil_of_fixed_len_zero (h : c.fixed_len 0) : ∀ as, (c.encoding as) = nil := 
by { intro _, rw encoding_eq_nil, exact λ _ _, c.code_nil_of_fixed_len_zero h _ }

lemma codeword_length_pos_of_fixed_len_pos {n : ℕ} (h₀ : 0 < n) (h₁ : c.fixed_len n) :
∀ a, 0 < (c a).length := λ a, (h₁ a).symm ▸ h₀

lemma code_ne_nil_of_fixed_len_pos {n : ℕ} (h₀ : 0 < n) (h₁ : c.fixed_len n) :
∀ a, (c a) ≠ nil := λ _, ne_nil_of_length_pos (c.codeword_length_pos_of_fixed_len_pos h₀ h₁ _)

lemma not_decodable_of_nil_codeword (h : ∃ a, (c a) = nil ) : ¬c.decodable :=
begin
  rw not_decodable_iff_exists_encodings_eq,
  rcases h with ⟨a, ha⟩,
  use [[a], nil],
  simp only [ ha, encoding_cons, encoding_nil, append_nil,
              eq_self_iff_true, ne.def, not_false_iff, and_self]
end

lemma decodable_of_fixed_length_pos_of_injective 
{n : ℕ} (h₀ : 0 < n) (h₁ : c.fixed_len n) (h₂ : injective c) : c.decodable :=
begin
  intros s t hst,
  induction t with aₜ t IH generalizing s,
  { refine eq_nil_of_length_eq_zero (mul_right_injective h₀ _), dsimp,
    rw ← c.len_encoding_eq_of_fixed_len h₁,
    simp only [c.len_encoding_eq_of_fixed_len h₁, hst, length, encoding_nil, mul_zero]
  },
  cases s with aₛ s,
  { simp only [encoding_nil, encoding_cons, nil_eq_append_iff] at hst,
    exact false.elim (c.code_ne_nil_of_fixed_len_pos h₀ h₁ _ hst.1)
  },
  { simp only [encoding_cons] at hst,
    rcases append_inj hst (c.len_fixed_of_fixed_len h₁ _ _) with ⟨hst₁, hst₂⟩,
    specialize h₂ hst₁, specialize IH hst₂, rw [h₂, IH]
  }
end

--- Need to be able to define linear codes, which are different but give rise to codes...
--- Codes are often define in terms of the codebook, really. Maybe a code should be
    -- a set of words in the alphabet (which is a language, in mathlib terms, I note, though this may not be helpful because conceptually they live inside the wider output space...).
    -- an injective (?) function attached to them. Honestly the thing is that a code is mostly about
    -- the codewords...

end code