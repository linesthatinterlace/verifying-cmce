import topology.metric_space.basic

lemma set.not_subsingleton_iff {α : Type*} {s : set α} : ¬ s.subsingleton ↔ ∃ x y ∈ s, x ≠ y :=
by simp_rw [set.subsingleton, not_forall]

open_locale ennreal

lemma le_edist_pi_iff {β : Type*} {π : β → Type*} [fintype β] [nonempty β]
  [Π b, pseudo_emetric_space (π b)] {f g : Π b, π b} {d : ℝ≥0∞} :
  d ≤ edist f g ↔ ∃ b, d ≤ edist (f b) (g b) :=
begin
  by_cases hd : ⊥ < d,
  { exact (finset.le_sup_iff hd).trans (by simp only [finset.mem_univ, exists_true_left]) },
  { rw not_bot_lt_iff at hd, rw hd, simp only [ennreal.bot_eq_zero, zero_le, exists_const] }
end

namespace emetric

open set
variables {α β : Type*} 

noncomputable def grain [has_edist α] (s : set α) := ⨅ (x ∈ s) (y ∈ s) (hxy : x ≠ y), edist x y

section has_edist
variables [has_edist α] {x y : α} {s : set α}

lemma le_grain_iff {d} : d ≤ grain s ↔ ∀ x y ∈ s, x ≠ y → d ≤ edist x y :=
by simp_rw [grain, le_infi_iff]

lemma grain_le_iff {d} : grain s ≤ d ↔ ∀ e, ((∀ x y ∈ s, x ≠ y → e ≤ edist x y) → e ≤ d) :=
by simp_rw [grain, infi_le_iff, le_infi_iff]

lemma le_grain_image_iff {d} {f : β → α} {s : set β} :
  d ≤ grain (f '' s) ↔ ∀ x y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) :=
by simp_rw [le_grain_iff, ball_image_iff]

lemma le_edist_of_le_grain {d} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (hd : d ≤ grain s) :
  d ≤ edist x y := le_grain_iff.1 hd x hx y hy hxy

lemma grain_le_edist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : grain s ≤ edist x y :=
le_edist_of_le_grain hx hy hxy le_rfl

lemma le_grain {d} (h : ∀ x y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ grain s := le_grain_iff.2 h

lemma grain_subsingleton (hs : s.subsingleton) : grain s = ∞ :=
eq_top_iff.2 (le_grain (λ x hx y hy hxy, false.elim (hxy (hs hx hy))))

@[simp] lemma grain_empty : grain (∅ : set α) = ∞ :=
grain_subsingleton subsingleton_empty

@[simp] lemma grain_singleton : grain ({x} : set α) = ∞ :=
grain_subsingleton subsingleton_singleton

lemma grain_Union_mem_option {ι : Type*} (o : option ι) (s : ι → set α) :
  grain (⋃ i ∈ o, s i) = ⨅ i ∈ o, grain (s i) := by cases o; simp

lemma grain_anti : @antitone (set α) _ _ _ grain :=
λ s t h, le_grain $ λ x hx y hy, grain_le_edist_of_mem (h hx) (h hy)

lemma grain_insert_le : grain (insert x s) ≤ ⨅ (y ∈ s) (hxy : x ≠ y), edist x y :=
begin
  simp_rw [le_infi_iff],
  refine λ _ hy hxy, grain_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy
end

lemma grain_pair_le_left (hxy : x ≠ y) : grain ({x, y} : set α) ≤ edist x y :=
grain_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

lemma grain_pair_le_right (hxy : x ≠ y) : grain ({x, y} : set α) ≤ edist y x :=
by rw pair_comm; exact grain_pair_le_left hxy.symm

lemma le_grain_pair : (edist x y) ⊓ (edist y x) ≤ grain ({x, y} : set α) :=
begin
  simp_rw [le_grain_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff],
  rintros a (rfl | rfl) b (rfl | rfl) hab; finish
end

lemma grain_pair_eq' (hxy : x ≠ y) : grain ({x, y} : set α) = (edist x y) ⊓ (edist y x) :=
le_antisymm (le_inf (grain_pair_le_left hxy) (grain_pair_le_right hxy)) le_grain_pair

end has_edist

section pseudo_emetric_space
variables [pseudo_emetric_space α] {x y z : α} {s t : set α}

lemma grain_pair_eq (hxy : x ≠ y) : grain ({x, y} : set α) = edist x y :=
begin
  nth_rewrite 0 [← min_self (edist x y)],
  convert grain_pair_eq' hxy using 2,
  rw edist_comm
end

lemma grain_insert : grain (insert x s) = (⨅ (y ∈ s) (hxy : x ≠ y), edist x y) ⊓ (grain s) :=
begin
  refine le_antisymm (le_min grain_insert_le (grain_anti (subset_insert _ _))) _,
  simp_rw [le_grain_iff, inf_le_iff, mem_insert_iff],
  rintros y (rfl | hy) z (rfl | hz) hyz,
  { exact false.elim (hyz rfl) },
  { exact or.inl (infi_le_of_le _ (infi₂_le hz hyz)) },
  { rw edist_comm, exact or.inl (infi_le_of_le _ (infi₂_le hy hyz.symm)) },
  { exact or.inr (grain_le_edist_of_mem hy hz hyz) }
end

lemma grain_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
  grain ({x, y, z} : set α) = (edist x y) ⊓ (edist x z) ⊓ (edist y z) :=
by simp_rw [  grain_insert, infi_insert, infi_singleton, grain_singleton,
              inf_top_eq, cinfi_pos hxy, cinfi_pos hyz, cinfi_pos hxz]

lemma grain_pi_le_of_le {π : β → Type*} [fintype β] [∀ b, pseudo_emetric_space (π b)]
  {s : Π (b : β), set (π b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ grain (s b) ) :
  c ≤ grain (set.pi univ s) :=
begin
  refine le_grain (λ x hx y hy hxy, _),
  rw function.ne_iff at hxy,
  haveI := nonempty_of_exists hxy,
  rcases hxy with ⟨i, hi⟩,
  rw mem_univ_pi at hx hy,
  exact le_edist_pi_iff.mpr ⟨i, (le_grain_iff.1 (h i) _ (hx _) _ (hy _) hi)⟩
end

end pseudo_emetric_space

end emetric

namespace metric

/- Do it all there. -/
section pseudo_metric_space
variables {α : Type*} [pseudo_metric_space α] {s : set α}

noncomputable def grain (s : set α) : ℝ := ennreal.to_real (emetric.grain s)

theorem grain_eq_infty_iff : emetric.grain s = ∞ ↔ s.subsingleton :=
begin
  split,
  rw emetric.grain, simp_rw infi_eq_top,
  intros H _ hx _ hy, by_contradiction hxy,
  exact edist_ne_top _ _ (H _ hx _ hy hxy),
  exact emetric.grain_subsingleton,
end

theorem grain_bounded_iff_not_subsingleton : emetric.grain s < ∞ ↔ ∃ (x ∈ s) (y ∈ s), x ≠ y :=
begin
  rw lt_top_iff_ne_top,
  refine iff.not_left _,
  push_neg,
  exact grain_eq_infty_iff
end

end pseudo_metric_space

end metric