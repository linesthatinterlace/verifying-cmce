import tactic
import topology.metric_space.basic
import order.filter.basic
open metric set
variables {X : Type*} [metric_space X] (ε r R: ℝ) (L : set X)

def sep_by : Prop := ∀ x y ∈ L, x ≠ y → ε ≤ dist x y

@[simp] lemma sep_by_iff : sep_by ε L ↔ ∀ x y ∈ L, x ≠ y → ε ≤ dist x y := iff.rfl

def net_by : Prop := sep_by ε L ∧ ∀ L', sep_by ε L' → L ≤ L' → L = L'

def eps_sep : Prop := ∃ ε, sep_by ε L

@[simp] lemma eps_sep_iff : eps_sep L ↔ ∃ ε, sep_by ε L := iff.rfl

def ud_of : Prop := ∀ y, set.subsingleton (ball y r ∩ L)

@[simp] lemma ud_of_iff : ud_of r L ↔ ∀ y, (ball y r ∩ L).subsingleton := iff.rfl

def rd_of : Prop := ∀ y, set.nonempty (closed_ball y R ∩ L)

@[simp] lemma rd_of_iff : rd_of R L ↔ ∀ y, (closed_ball y R ∩ L).nonempty := iff.rfl

theorem metric.mem_ball_comm' {α : Type*} [pseudo_metric_space α] {x y : α} {ε : ℝ} : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', ←mem_ball]

theorem metric.mem_closed_ball_comm {α : Type*} [pseudo_metric_space α] {x y : α} {ε : ℝ} :
x ∈ metric.closed_ball y ε ↔ y ∈ metric.closed_ball x ε :=
by by rw [mem_closed_ball', ←mem_closed_ball]
example {P Q : Prop} (p : P ∨ P) : P  :=
begin
  refine or.dcases_on p (λ _, _) (λ _, _),
end
def uniformly_discrete : Prop := ∃ r, ud_of r L

@[simp] lemma uniformly_discrete_iff : uniformly_discrete L ↔ ∃ r, ud_of r L := iff.rfl

def relatively_dense : Prop := ∃ R, rd_of R L

@[simp] lemma relatively_dense_iff : relatively_dense L ↔ ∃ R, rd_of R L := iff.rfl

def delone_set : Prop := uniformly_discrete L ∧ relatively_dense L

@[simp] lemma delone_set_iff : delone_set L ↔ (∃ r, ud_of r L) ∧ (∃ R, rd_of R L) := iff.rfl

def delone_set_of : Prop := ud_of r L ∧ rd_of R L

@[simp] lemma delone_of_iff : delone_set_of r R L ↔ ud_of r L ∧ rd_of R L := iff.rfl

lemma delone_sets_eq_union_delone_of : delone_set L ↔ ∃ r R, delone_set_of r R L :=
by simp_rw [delone_set_iff, delone_of_iff, exists_and_distrib_left, exists_and_distrib_right]