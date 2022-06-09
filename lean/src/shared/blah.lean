import linear_algebra.basis
import data.matrix.notation

open matrix
variables (R : Type) (V : Type) [ring R] [add_comm_group V] [module R V]
-- (1 + (matrix.col u).mul (matrix.row v))
lemma better_form (v1 v2 v3 v4 : V) : 
![v1 - v2, v2 - v3, v3 - v4, v4] = ![v1, v2, v3, v4] - fin.snoc (fin.tail (![v1, v2, v3, v4])) 0 :=
by simp [vec_head, vec_tail, fin.snoc, fin.tail]; refl

lemma snoc_tail_lin_indep (v : fin 4 → V) (lin_indep : linear_independent R v) : 
linear_independent R (v - fin.snoc (fin.tail v) 0) :=
begin
  simp_rw fintype.linear_independent_iff at ⊢ lin_indep, intros g hg i,
  suffices hli :  finset.univ.sum (λ (i : fin 4), 
                  (g - fin.cons 0 (fin.init g)) i • v i) = 0,
  { specialize lin_indep _ hli,
    have g0 : g 0 -   0 = 0 := lin_indep 0,               rw sub_zero at g0,
    have g1 : g 1 - g 0 = 0 := lin_indep 1, rw g0 at g1,  rw sub_zero at g1,
    have g2 : g 2 - g 1 = 0 := lin_indep 2, rw g1 at g2,  rw sub_zero at g2,
    have g3 : g 3 - g 2 = 0 := lin_indep 3, rw g2 at g3,  rw sub_zero at g3,
    fin_cases i; [exact g0, exact g1, exact g2, exact g3] },
  
  simp [fin.sum_univ_succ, smul_sub, sub_smul] at ⊢ hg,
  change  g 0 • v 0 + (g 1 • v 1 - g 0 • v 1 + 
          (g 2 • v 2 - g 1 • v 2 + (g 3 • v 3 - g 2 • v 3))) = 0,
  change  g 0 • v 0 - g 0 • v 1 + (g 1 • v 1 - 
          g 1 • v 2 + (g 2 • v 2 - g 2 • v 3 + (g 3 • v 3 - g 3 • 0))) = 0 at hg,
  rw [smul_zero, sub_zero] at hg, simp_rw [sub_eq_add_neg] at ⊢ hg,
  nth_rewrite 2 add_comm, nth_rewrite 4 add_comm, nth_rewrite 5 add_comm, simp_rw add_assoc at ⊢ hg,
  exact hg
end

example (v1 v2 v3 v4 : V) (lin_indep : linear_independent R ![v1, v2, v3, v4]) : 
linear_independent R ![v1-v2, v2-v3, v3 - v4, v4] := 
by rw better_form ; exact snoc_tail_lin_indep _ _ _ lin_indep