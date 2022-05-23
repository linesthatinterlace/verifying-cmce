import tactic.basic
import algebra.order.monoid
import order.succ_pred.basic
open function

universe u
variable {α : Type u}

namespace with_top
variables {a b c d : with_top α}

-- Generalisations that are possible.

lemma not_top_le_coe' [has_le α] (a : α) : ¬ (⊤ : with_top α) ≤ ↑a :=
by simp [has_le.le, some_eq_coe]

lemma ne_top_of_lt' [has_lt α] (h : a < b) : a ≠ ⊤ :=
by { rintro rfl, simpa [has_lt.lt, some_eq_coe] using h }

lemma lt_top_of_ne_top [has_lt α] (h : a ≠ ⊤) : a < ⊤ :=
by { cases a, exact (h rfl).elim, exact some_lt_none _ }

lemma lt_top_iff_ne_top' [has_lt α] : a < ⊤ ↔ a ≠ ⊤ := ⟨λ H, ne_top_of_lt' H, lt_top_of_ne_top⟩

-- add_lt_add lemmas. Many, MANY options.

theorem add_lt_add_of_lt_of_lt_of_ne_left_top [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (<)]
(hb : b ≠ ⊤) (hab : a < b) (hcd : c < d) : a + c < b + d :=
calc  a + c < b + c : with_top.add_lt_add_right (ne_top_of_lt hcd) hab
      ...   < b + d : with_top.add_lt_add_left hb hcd

theorem add_lt_add_of_lt_of_lt_of_ne_right_top [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (<)]
(hd : d ≠ ⊤) (hab : a < b) (hcd : c < d) : a + c < b + d :=
calc  a + c < a + d : with_top.add_lt_add_left (ne_top_of_lt hab) hcd
      ...   < b + d : with_top.add_lt_add_right hd hab

theorem add_lt_add_of_lt_of_lt_of_cov_lt_cov_swap_lt [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (<)]
(hab : a < b) (hcd : c < d) : a + c < b + d :=
begin
  cases b,
  { cases d,
    { rw [none_eq_top, add_top, ← @top_add _ _ c],
      exact with_top.add_lt_add_right (ne_top_of_lt' hcd) hab },
    { exact add_lt_add_of_lt_of_lt_of_ne_right_top (coe_ne_top) hab hcd }
  },  exact add_lt_add_of_lt_of_lt_of_ne_left_top (coe_ne_top) hab hcd
end

theorem add_lt_add_of_lt_of_lt_cov_lt [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (≤)]
(hab : a < b) (hcd : c < d) : a + c < b + d :=
calc  a + c < a + d : with_top.add_lt_add_left (ne_top_of_lt hab) hcd
      ...   ≤ b + d : add_le_add_right hab.le _

theorem add_lt_add_of_lt_of_lt_cov_swap_lt [has_add α] [preorder α]
[covariant_class α α (+) (≤)] [covariant_class α α (swap (+)) (<)]
(hab : a < b) (hcd : c < d) : a + c < b + d :=
calc  a + c < b + c : with_top.add_lt_add_right (ne_top_of_lt hcd) hab
      ...   ≤ b + d : add_le_add_left hcd.le b

theorem add_lt_add_of_le_of_lt_of_left_ne_top [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (≤)]
(ha : a ≠ ⊤) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
calc  a + c < a + d : with_top.add_lt_add_left ha hcd
      ...   ≤ b + d : add_le_add_right hab _

theorem add_lt_add_of_le_of_lt_of_right_ne_top [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (≤)]
(hb : b ≠ ⊤) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
calc  a + c ≤ b + c : add_le_add_right hab _
      ...   < b + d : with_top.add_lt_add_left hb hcd

theorem add_lt_add_of_lt_of_le_of_left_ne_top [has_add α] [preorder α]
[covariant_class α α (+) (≤)] [covariant_class α α (swap (+)) (<)]
(hc : c ≠ ⊤) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
calc  a + c < b + c : with_top.add_lt_add_right hc hab
      ...   ≤ b + d : add_le_add_left hcd _

theorem add_lt_add_of_lt_of_le_of_right_ne_top [has_add α] [preorder α]
[covariant_class α α (+) (≤)] [covariant_class α α (swap (+)) (<)]
(hd : d ≠ ⊤) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
calc  a + c ≤ a + d : add_le_add_left hcd _
      ...   < b + d : with_top.add_lt_add_right hd hab

end with_top

namespace with_bot
variables {a b c d : with_bot α}

lemma not_coe'_le_bot [has_le α] (a : α) : ¬ ↑a ≤ (⊥ : with_bot α) :=
@with_top.not_top_le_coe' (order_dual α) _ _

lemma ne_bot_of_gt' [has_lt α] (h : a < b) : b ≠ ⊥ :=
@with_top.ne_top_of_lt' (order_dual α) _ _ _ h

lemma lt_top_of_ne_top [has_lt α] (h : a ≠ ⊥) : ⊥ < a :=
@with_top.lt_top_of_ne_top (order_dual α) _ _ h

lemma lt_top_iff_ne_top' [has_lt α] : ⊥ < a ↔ a ≠ ⊥ := 
@with_top.lt_top_iff_ne_top' (order_dual α) _ _

-- add_lt_add lemmas. Many, MANY options.

theorem add_lt_add_of_lt_of_lt_of_ne_left_top [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (<)]
(ha : a ≠ ⊥) (hab : a < b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_lt_of_ne_left_top (order_dual α) _ _ _ _ _ _ _ _ ha hab hcd

theorem add_lt_add_of_lt_of_lt_of_ne_right_top [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (<)]
(hc : c ≠ ⊥) (hab : a < b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_lt_of_ne_right_top (order_dual α) _ _ _ _ _ _ _ _ hc hab hcd

theorem add_lt_add_of_lt_of_lt_of_cov_lt_cov_swap_lt [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (<)]
(hab : a < b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_lt_of_cov_lt_cov_swap_lt (order_dual α) _ _ _ _ _ _ _ _ hab hcd

theorem add_lt_add_of_lt_of_lt_cov_lt [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (≤)]
(hab : a < b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_lt_cov_lt (order_dual α) _ _ _ _ _ _ _ _ hab hcd

theorem add_lt_add_of_lt_of_lt_cov_swap_lt [has_add α] [preorder α]
[covariant_class α α (+) (≤)] [covariant_class α α (swap (+)) (<)]
(hab : a < b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_lt_cov_swap_lt (order_dual α) _ _ _ _ _ _ _ _ hab hcd

theorem add_lt_add_of_le_of_lt_of_left_ne_bot [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (≤)]
(ha : a ≠ ⊥) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_le_of_lt_of_right_ne_top (order_dual α) _ _ _ _ _ _ _ _ ha hab hcd

theorem add_lt_add_of_le_of_lt_of_right_ne_bot [has_add α] [preorder α]
[covariant_class α α (+) (<)] [covariant_class α α (swap (+)) (≤)]
(hb : b ≠ ⊥) (hab : a ≤ b) (hcd : c < d) : a + c < b + d :=
@with_top.add_lt_add_of_le_of_lt_of_left_ne_top (order_dual α) _ _ _ _ _ _ _ _ hb hab hcd

theorem add_lt_add_of_lt_of_le_of_left_ne_bot [has_add α] [preorder α]
[covariant_class α α (+) (≤)] [covariant_class α α (swap (+)) (<)]
(hc : c ≠ ⊥) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_le_of_right_ne_top (order_dual α) _ _ _ _ _ _ _ _ hc hab hcd

theorem add_lt_add_of_lt_of_le_of_right_ne_bot [has_add α] [preorder α]
[covariant_class α α (+) (≤)] [covariant_class α α (swap (+)) (<)]
(hd : d ≠ ⊥) (hab : a < b) (hcd : c ≤ d) : a + c < b + d :=
@with_top.add_lt_add_of_lt_of_le_of_left_ne_top (order_dual α) _ _ _ _ _ _ _ _ hd hab hcd

end with_bot