import data.zmod.basic
import algebra.char_p.two

namespace nat
lemma zero_or_one_of_lt_two : ∀ {m : ℕ}, m < 2 → m = 0 ∨ m = 1
| 0 _ := or.inl rfl
| 1 _ := or.inr rfl
| (n + 2) h := false.elim (n.not_lt_zero (lt_of_add_lt_add_right h))
end nat

namespace zmod

variables (a b : zmod 2)

lemma val_eq_one {a : zmod 2}: a.val = 1 ↔ a = 1 :=
by { simp_rw ← zmod.val_one 2, split; intro h; [apply zmod.val_injective _ h, rw h] }

lemma zmod_two_cases : a = 0 ∨ a = 1 :=
by { rw ← val_eq_one, rw ← val_eq_zero, exact nat.zero_or_one_of_lt_two (val_lt _) }

lemma zmod_two_val_eq : a.val = if a = 1 then 1 else 0 :=
by { symmetry, rw ite_eq_iff, rcases zmod_two_cases a with rfl | rfl; simp [val_one] }

lemma zmod_two_val_neg_eq : (-a).val = a.val :=
by { rcases zmod_two_cases a with rfl | rfl; simp [neg_one_eq_one_iff] }

lemma zmod_sub_val_eq : (a - b).val = if a ≠ b then 1 else 0 :=
by {  rcases zmod_two_cases (a - b) with h | h;
      [rw sub_eq_zero at h, rw sub_eq_iff_eq_add at h];
      rw h; simp [zmod_two_val_eq, add_assoc] }

lemma zmod_sub_val_comm : (a - b).val = (b - a).val :=
by { simp_rw [zmod_sub_val_eq, ne_comm] }

end zmod