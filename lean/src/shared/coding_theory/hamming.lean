import algebra.big_operators.basic

namespace coding_theory

section hamming

open_locale big_operators
variables {n : ℕ} {K : Type*} (x y z : fin n → K)

section decidable_eq
variable [decidable_eq K]

open finset function

def ham_dist : ℕ := (filter (λ i, x i ≠ y i) univ).card

@[simp]
lemma ham_dist_eq : ham_dist x y = (filter (λ i, x i ≠ y i) univ).card := rfl

lemma ham_dist_eq_sum_ite : ham_dist x y = ∑ i, if x i ≠ y i then 1 else 0 :=
by { simp, rw [sum_ite, ← card_eq_sum_ones, sum_const_zero, zero_add] }

@[simp]
lemma ham_dist_self_eq_zero : ham_dist x x = 0 := by simp

lemma ham_dist_comm : ham_dist x y = ham_dist y x :=
by { simp, congr, ext, exact ne_comm }

lemma zero_le_ham_dist : 0 ≤ ham_dist x y := zero_le _

lemma ham_dist_eq_zero_iff_eq : ham_dist x y = 0 ↔ x = y :=
begin
  split; intros h; [refine funext _, rw h]; [contrapose h, exact ham_dist_self_eq_zero _],
  rw [ham_dist_eq, card_eq_zero, filter_eq_empty_iff],
  simpa only [mem_univ, not_not, forall_true_left]
end

lemma ham_dist_pos_iff_neq : 0 < ham_dist x y ↔ x ≠ y :=
begin
  rw [ne.def, ← ham_dist_eq_zero_iff_eq], split; intros h; 
  [intro c, exact lt_of_le_of_ne (zero_le_ham_dist _ _) (ne.symm h)],
  rw c at h, exact nat.not_lt_zero _ h
end

lemma ham_dist_le : ham_dist x y ≤ ham_dist x z + ham_dist z y :=
begin
  simp_rw ham_dist_eq,
  refine le_trans (card_le_of_subset _) (card_union_le _ _),
  intros i, simp_rw [mem_union, mem_filter],
  simp only [mem_univ, ne.def, true_and], contrapose!,
  exact λ ⟨_, _⟩, eq.trans (by assumption) (by assumption)
end

section has_zero
variable [has_zero K]

def ham_wt : ℕ := ham_dist x 0

@[simp]
lemma ham_wt_eq : ham_wt x = (filter (λ i, x i ≠ 0) univ).card := ham_dist_eq _ _

lemma ham_wt_eq_sum_ite : ham_wt x = ∑ i, if x i ≠ 0 then 1 else 0 := ham_dist_eq_sum_ite _ _

@[simp]
lemma ham_wt_zero_eq_zero : ham_wt (0 : fin n → K) = 0 := ham_dist_self_eq_zero _

lemma zero_le_ham_wt : 0 ≤ ham_wt x := zero_le_ham_dist _ _

lemma ham_wt_eq_zero_iff_zero : ham_wt x = 0 ↔ x = 0 := ham_dist_eq_zero_iff_eq _ _

lemma ham_wt_pos_iff_neq : 0 < ham_wt x ↔ x ≠ 0 := ham_dist_pos_iff_neq _ _

end has_zero

section add_group
variable [add_group K]

lemma ham_dist_eq_wt : ham_dist x y = ham_wt (x - y) :=
by simp_rw [ham_dist_eq, ham_wt_eq, pi.sub_apply, sub_ne_zero]

end add_group

section mul_zero_class

variables [mul_zero_class K] (t : K)

lemma wt_smul_le : ham_wt (t • x) ≤ (if t ≠ 0 then 1 else 0) * (ham_wt x) :=
begin
  split_ifs,
  { simp only [ ham_wt_eq, pi.smul_apply, smul_eq_mul, ne.def, one_mul],
    refine card_le_of_subset (λ _, _), simp only [mem_filter, mem_univ, true_and],
    exact right_ne_zero_of_mul },
  { rw not_not at h, simp only [h, zero_smul, ham_wt_zero_eq_zero, zero_mul] }
end

end mul_zero_class

end decidable_eq
end hamming


/-
namespace discrete

variables 

def dist {K : Type*} [decidable_eq K] := λ x y : K, if x = y then (0 : ℝ) else 1

@[simp]
def dist_eq {K : Type*} [decidable_eq K] (x y : K) : dist x y = if x = y then 0 else 1 := rfl

def pseudo_metric_space (K : Type*) [decidable_eq K] : pseudo_metric_space K := {
  dist := discrete.dist,
  dist_self := λ _, by simp [dist_eq],
  dist_comm := λ x y, by simp_rw [dist, eq_comm],
  dist_triangle := λ x y z,
  by {  simp[dist], split_ifs;
        try {simp only [  add_zero, zero_add, zero_le_one,
                          one_add_one_eq_two, one_le_two, zero_le_two]},
        finish }
}


def metric_space (K : Type*) [decidable_eq K] [has_zero K] : metric_space K :=
{ ..(discrete.pseudo_metric_space K),
  eq_of_dist_eq_zero := λ x y h, by { by_contradiction c, simp at h,
                                      rw ite_eq_left_iff at h, exact one_ne_zero (h c) },

  
}

instance [add_comm_group K] : normed_group K := {
  norm := λ x, dist x 0,
  dist_eq := λ x y, by simp_rw [dist, sub_eq_zero] }

instance [non_unital_ring K] : non_unital_normed_ring K := {
  norm_mul := begin  end,
  }

end discrete


namespace fin



instance : uniform_space (fin n) := ⊥

noncomputable instance : has_dist (fin n) := ⟨λ x y, dist (x : ℝ) y⟩

lemma dist_eq (x y : fin n) : dist x y = |x - y| := rfl

lemma dist_coe_nat (x y : fin n) : dist (x : ℕ) (y : ℕ) = dist x y := rfl

@[norm_cast, simp] theorem dist_cast_real {n : ℕ} (x y : (fin n)) : dist (x : ℝ) y = dist x y := rfl

lemma pairwise_one_le_dist : pairwise (λ x y : fin n, 1 ≤ dist x y) :=
begin
  intros x y hxy,
  rw ← dist_coe_nat,
  apply nat.pairwise_one_le_dist,
  contrapose! hxy,
  apply fin.coe_injective hxy
end
open metric

lemma uniform_embedding_coe_real : uniform_embedding (coe : (fin n) → ℝ) :=
uniform_embedding_bot_of_pairwise_le_dist real.zero_lt_one pairwise_one_le_dist

lemma closed_embedding_coe_real : closed_embedding (coe : (fin n) → ℝ) :=
closed_embedding_of_pairwise_le_dist real.zero_lt_one pairwise_one_le_dist

noncomputable instance : metric_space (fin n) := uniform_embedding_coe_real.comap_metric_space _

lemma dist_0_eq {x : fin (n + 1)} (h : x ≤ n / 2) : dist x 0 = x := 
begin
  split_ifs; rw dist_eq; simp, norm_cast,
end

end fin

variables (p : ℕ) [fact p.prime]
instance : normed_field (zmod p) := {! !}
end zmod
def codeword (n : ℕ) := pi_Lp 1 (λ x : fin n, zmod 2)

#check (0 : pi_Lp 1 (λ x : fin 3, zmod 2))
-/

end coding_theory