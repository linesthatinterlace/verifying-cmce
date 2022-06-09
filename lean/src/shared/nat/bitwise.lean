import tactic

open list function
namespace nat

@[simp] lemma bit_ff : bit ff = bit0 := rfl
@[simp] lemma bit_tt : bit tt = bit1 := rfl

@[simp] lemma bit_eq_zero_iff {n : ℕ} {b : bool} : bit b n = 0 ↔ n = 0 ∧ b = ff :=
by { cases b; norm_num [bit0_eq_zero, nat.bit1_ne_zero] }

@[simp] lemma bit_ne_zero_iff {n : ℕ} {b : bool} : bit b n ≠ 0 ↔ n ≠ 0 ∨ b = tt :=
by { cases b; norm_num }

section binary_rec
universe u

def binary_rec' {C : nat → Sort u} (z : C 0)
  (f : ∀ b n, bit b n ≠ 0 → C n → C (bit b n)) : Π n, C n :=
binary_rec z (λ b n,  if h : bit b n = 0
                      then by rw h; rw bit_eq_zero_iff at h; rw h.1; exact id 
                      else f _ _ h)


lemma binary_rec_eq_bit_ne_zero {C : nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) {b n}
  (hn : bit b n ≠ 0) : binary_rec z f (bit b n) = f b n (binary_rec z f n) :=
by { rw binary_rec, simp [hn],
    generalize : binary_rec._main._pack._proof_2 _ = e, revert e,
    rw [bodd_bit, div2_bit], intros, refl }

lemma binary_rec_eq' {C : nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)} (b n) 
  (hf : f ff 0 z = z) : binary_rec z f (bit b n) = f b n (binary_rec z f n) :=
begin
  cases b,
  { by_cases hn : (n = 0),
    { rw [hn, binary_rec], simp [hf] },
    { exact binary_rec_eq_bit_ne_zero _ _ (bit_ne_zero _ hn) }
  },
  { exact binary_rec_eq_bit_ne_zero _ _ (add_one_ne_zero _) }
end

end binary_rec

section bits

@[simp] lemma bits_zero : bits 0 = [] := binary_rec_zero _ _

@[simp] lemma bits_bit_ne_zero {b : bool} {n : ℕ} : bit b n ≠ 0 → (bit b n).bits = b :: n.bits := 
begin
  refine nat.bit_cases_on n (λ b n, _),
  exact λ H, by rw [bits, binary_rec_eq_bit_ne_zero _ _ H]
end

end bits

section test_bits
@[simp] lemma zero_test_bit (i : ℕ) : test_bit 0 i = ff := by simp [test_bit]

def bits_test (B : list bool) (i : ℕ) : bool := (B.nth i).get_or_else ff

lemma bits_test_lt {B : list bool} {i} (h : i < B.length) : 
bits_test B i = B.nth_le i h := by rw [bits_test, nth_le_nth h, option.get_or_else_some]

lemma bits_test_ge {B : list bool} {i} (h : B.length ≤ i) :
bits_test B i = ff := by rw [bits_test, nth_len_le h, option.get_or_else_none]

@[simp] lemma bits_test_nil {i : ℕ} : bits_test [] i = ff := rfl

@[simp] lemma bits_test_cons_zero {B : list bool} {b} : bits_test (b :: B) 0 = b := rfl

@[simp] lemma bits_test_cons_succ (B : list bool) {b} {i : ℕ} : 
  bits_test (b :: B) i.succ = bits_test B i := 
begin
  by_cases h₁ : i < B.length,
  { have h₂ : i.succ < (b :: B).length, exact succ_lt_succ h₁,
    rw [bits_test_lt h₁, bits_test_lt h₂], refl
  },
  { rw not_lt at h₁,
    have h₂ : (b :: B).length ≤ i.succ, exact succ_le_succ h₁,
    rw [bits_test_ge h₁, bits_test_ge h₂]
  }
end


lemma test_bot_eq_bits_test {n i : ℕ} : test_bit n i = bits_test (bits n) i :=
begin
  induction n using nat.binary_rec' with b n hbn IH generalizing i,
  { rw [bits_zero, bits_test_nil, zero_test_bit] },
  { rw bits_bit_ne_zero hbn, cases i,
    { rw [test_bit_zero, bits_test_cons_zero] },
    { rw [test_bit_succ, bits_test_cons_succ, IH] } }
end

end test_bits

section of_bits
def of_bits : list bool → ℕ
| [] := 0
| (b :: B) := bit b (of_bits B)

lemma of_bits_nil : of_bits [] = 0 := rfl

lemma of_bits_cons (b : bool) (B : list bool) :
  of_bits (b :: B) = bit b (of_bits B) := rfl

end of_bits

section bits_of_bits

lemma of_bits_bits_left_inverse : left_inverse of_bits bits :=
begin
  intros n, induction n using nat.binary_rec' with b n hn ih,
  { rw [bits_zero, of_bits_nil] },
  { rw [bits_bit_ne_zero hn, of_bits_cons, ih] }
end

lemma of_bits.surjective : surjective of_bits := 
right_inverse.surjective of_bits_bits_left_inverse

lemma bits.injective : injective bits := 
left_inverse.injective of_bits_bits_left_inverse

end bits_of_bits

end nat