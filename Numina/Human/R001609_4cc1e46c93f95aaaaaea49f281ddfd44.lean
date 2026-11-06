import Mathlib

open Finset Equiv

/- We show that if a > 0, then a / (a - x) → -∞ when x →+ a -/
lemma tendsto_atBot_right_of_pos {a b : ℝ} (ha : a > 0) : Filter.Tendsto (fun x => a / (a - x)) (nhdsWithin a (Set.Ioo a b)) Filter.atBot := by
  apply Filter.Tendsto.mul_atBot (C := a)
  · exact ha
  · exact tendsto_const_nhds
  · apply Filter.tendsto_neg_atTop_iff.mp
    simp [neg_inv]
    apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
    refine Metric.tendsto_nhdsWithin_nhdsWithin.mpr ?_
    intro ε hε
    use ε, hε
    intro x hx hdist
    simp at hx
    simp [dist] at hdist
    simp [hx.1, hdist]

/- We show that if a < 0, then a / (a - x) → +∞ when x →+a -/
lemma tendsto_atTop_right_of_neg {a b : ℝ} (ha : a < 0) : Filter.Tendsto (fun x => a / (a - x)) (nhdsWithin a (Set.Ioo a b)) Filter.atTop := by
  apply Filter.Tendsto.neg_mul_atBot (C := a)
  · exact ha
  · exact tendsto_const_nhds
  · apply Filter.tendsto_neg_atTop_iff.mp
    simp [neg_inv]
    apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
    refine Metric.tendsto_nhdsWithin_nhdsWithin.mpr ?_
    intro ε hε
    use ε, hε
    intro x hx hdist
    simp at hx
    simp [dist] at hdist
    simp [hx.1, hdist]

/- We show that if b > 0, then b / (b - x) → +∞ when x →-b -/
lemma tendsto_atTop_left_of_pos {a b : ℝ} (hb : b > 0) : Filter.Tendsto (fun x => b / (b - x)) (nhdsWithin b (Set.Ioo a b)) Filter.atTop := by
  apply Filter.Tendsto.mul_atTop (C := b)
  · exact hb
  · exact tendsto_const_nhds
  · apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
    refine Metric.tendsto_nhdsWithin_nhdsWithin.mpr ?_
    intro ε hε
    use ε, hε
    intro x hx hdist
    simp at hx
    simp [dist, abs_sub_comm] at hdist
    simp [hx.2, hdist]

/- We show that if b < 0, then b / (b - x) → -∞ when x →- b -/
lemma tendsto_atBot_left_of_neg {a b : ℝ} (hb : b < 0) : Filter.Tendsto (fun x => b / (b - x)) (nhdsWithin b (Set.Ioo a b)) Filter.atBot := by
  apply Filter.Tendsto.neg_mul_atTop (C := b)
  · exact hb
  · exact tendsto_const_nhds
  · apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
    refine Metric.tendsto_nhdsWithin_nhdsWithin.mpr ?_
    intro ε hε
    use ε, hε
    intro x hx hdist
    simp at hx
    simp [dist, abs_sub_comm] at hdist
    simp [hx.2, hdist]

/- We prove that f is continuous on the interval (a_i, a_{i+1}) -/
lemma continuousOn_f (a : Fin n → ℝ) (ha : StrictMono a) (f : ℝ → ℝ) (hf : f = fun x => ∑ i : Fin n, a i / (a i - x)) {i : ℕ} (hi : i + 1 < n) : ContinuousOn f (Set.Ioo (a ⟨i, by exact Nat.lt_of_succ_lt hi⟩) (a ⟨i + 1, hi⟩)) := by
  rw [hf]
  apply continuousOn_finset_sum
  intro ⟨j, hj⟩ _
  apply ContinuousOn.div
  · exact continuousOn_const
  · apply ContinuousOn.sub
    · exact continuousOn_const
    · apply continuousOn_id'
  · intro x hx
    simp at hx
    by_cases hj : j ≥ i + 1
    · apply ne_of_gt
      simp
      apply lt_of_lt_of_le hx.2
      apply StrictMono.monotone ha
      simp
      exact hj
    · simp at hj
      apply ne_of_lt
      simp
      apply lt_of_le_of_lt ?_ hx.1
      apply StrictMono.monotone ha
      simp
      exact Nat.le_of_lt_succ hj

/- We show that the finite sum of all terms except a_i/ (a_i-x) is bounded when x → a_i. -/
lemma tendsTo_nhds {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a) {i : ℕ} (hi : i + 1 < n) :
    Filter.Tendsto (fun x ↦ ∑ j ∈ univ.erase ⟨i, by exact Nat.lt_of_succ_lt hi⟩, a j / (a j - x)) (nhdsWithin (a ⟨i, by exact Nat.lt_of_succ_lt hi⟩) s)
    (nhds (∑ j ∈ univ.erase ⟨i, by exact Nat.lt_of_succ_lt hi⟩, a j / (a j - a ⟨i, by exact Nat.lt_of_succ_lt hi⟩))) := by
  -- In fact, when x → a_i, ∑ j ∈ univ.erase ⟨i, Nat.lt_of_succ_lt hi⟩, a j / (a j - x) → ∑ j ∈ univ.erase ⟨i, Nat.lt_of_succ_lt hi⟩, a i / (a i - x).
  let δ : ℝ := min ((a ⟨i + 1, hi⟩ - a ⟨i, Nat.lt_of_succ_lt hi⟩) / 2)
      (if i > 0 then (a ⟨i, Nat.lt_of_succ_lt hi⟩ - a ⟨i - 1, by apply lt_of_le_of_lt (b := i); simp; exact Nat.lt_of_succ_lt hi⟩) / 2 else (a ⟨i + 1, hi⟩ - a ⟨i, Nat.lt_of_succ_lt hi⟩) / 2)
  have hδpos : 0 < δ := by
    simp [δ]
    by_cases hi : i > 0
    · simp [hi]
      constructor
      · apply ha
        simp
      · apply ha
        simp
        exact hi
    · simp [hi]
      apply ha
      simp
  have hadd_lt : a ⟨i, Nat.lt_of_succ_lt hi⟩ + δ < a ⟨i + 1, hi⟩ := by
    apply lt_of_le_of_lt (b := a ⟨i, Nat.lt_of_succ_lt hi⟩ + (a ⟨i + 1, hi⟩ - a ⟨i, Nat.lt_of_succ_lt hi⟩) / 2)
    · gcongr
      apply min_le_left
    . apply sub_pos.mp
      ring_nf
      field_simp
      apply ha
      simp
  have hlt_sub (h : i > 0) : a ⟨i - 1, by apply lt_of_le_of_lt (b := i); simp; exact Nat.lt_of_succ_lt hi⟩ < a ⟨i, Nat.lt_of_succ_lt hi⟩ - δ := by
    simp [δ, h]
    apply lt_of_lt_of_le (b := a ⟨i, Nat.lt_of_succ_lt hi⟩ - (a ⟨i, Nat.lt_of_succ_lt hi⟩ - a ⟨i - 1, by apply lt_of_le_of_lt (b := i); simp; exact Nat.lt_of_succ_lt hi⟩) / 2)
    · apply sub_pos.mp
      ring_nf
      field_simp
      apply ha
      simp
      exact h
    · gcongr
      apply min_le_right
  -- The proof proceeds by applying the continuity of f.
  apply tendsto_nhdsWithin_of_tendsto_nhds
  apply ContinuousAt.tendsto
  apply ContinuousOn.continuousAt (s := Set.Icc (a ⟨i, Nat.lt_of_succ_lt hi⟩ - δ) (a ⟨i, Nat.lt_of_succ_lt hi⟩ + δ))
  apply continuousOn_finset_sum
  · intro ⟨j, hasSum_le_inj⟩ hj_mem
    apply ContinuousOn.div
    · exact continuousOn_const
    · apply ContinuousOn.sub
      · exact continuousOn_const
      · apply continuousOn_id'
    · intro x hx
      by_cases hj : j ≥ i + 1
      · apply ne_of_gt
        simp
        apply lt_of_le_of_lt hx.2
        apply lt_of_lt_of_le hadd_lt
        apply StrictMono.monotone ha
        simp
        exact hj
      · simp at hj hj_mem
        have hj : j < i := by
          apply lt_of_le_of_ne ?_ hj_mem
          exact Nat.le_of_lt_succ hj
        apply ne_of_lt
        simp
        apply lt_of_lt_of_le ?_ hx.1
        apply lt_of_le_of_lt (b := a ⟨i - 1, by apply lt_of_le_of_lt (b := i); simp; exact Nat.lt_of_succ_lt hi⟩)
        · apply StrictMono.monotone ha
          simp
          apply Nat.le_sub_one_of_lt hj
        · apply hlt_sub
          exact Nat.zero_lt_of_lt hj
  · simp
    exact hδpos

/- We show that the finite sum of all terms except a (i + 1) / (a_{i+1}-x) is bounded when x → a_{i+1}. -/
lemma tendsTo_nhds_succ {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a) {i : ℕ} (hi : i + 1 < n) :
    Filter.Tendsto (fun x ↦ ∑ j ∈ univ.erase ⟨i + 1, hi⟩, a j / (a j - x)) (nhdsWithin (a ⟨i + 1, hi⟩) s)
    (nhds (∑ j ∈ univ.erase ⟨i + 1, hi⟩, a j / (a j - a ⟨i + 1, hi⟩))) := by
  -- In fact, ∑ j ∈ univ.erase ⟨i + 1, hi⟩, a j / (a j - a ⟨i + 1, hi⟩ → ∑ j ∈ univ.erase ⟨i + 1, hi⟩, a (i + 1) / (a (i + 1) - x) when x → a (i + 1).
  let δ : ℝ := min ((a ⟨i + 1, hi⟩ - a ⟨i, Nat.lt_of_succ_lt hi⟩) / 2)
      (if hi' : i + 2 < n then (a ⟨i + 2, hi'⟩ - a ⟨i + 1, hi⟩) / 2 else (a ⟨i + 1, hi⟩ - a ⟨i, Nat.lt_of_succ_lt hi⟩) / 2)
  have hδpos : 0 < δ := by
    simp [δ]
    by_cases hi : i + 2 < n
    · simp [hi]
      constructor
      · apply ha
        simp
      · apply ha
        simp
    · simp [hi]
      apply ha
      simp
  have hlt_sub : a ⟨i, Nat.lt_of_succ_lt hi⟩ < a ⟨i + 1, hi⟩ - δ := by
    apply lt_of_lt_of_le (b := a ⟨i + 1, hi⟩ - (a ⟨i + 1, hi⟩ - a ⟨i, Nat.lt_of_succ_lt hi⟩) / 2)
    . apply sub_pos.mp
      ring_nf
      field_simp
      apply ha
      simp
    · gcongr
      apply min_le_left
  have hadd_lt (h : i + 2 < n) : a ⟨i + 2, h⟩ > a ⟨i + 1, hi⟩ + δ := by
    simp [δ, h]
    apply lt_of_le_of_lt (b := a ⟨i + 1, hi⟩ + (a ⟨i + 2, h⟩ - a ⟨i + 1, hi⟩) / 2)
    · gcongr
      apply min_le_right
    · apply sub_pos.mp
      ring_nf
      field_simp
      apply ha
      simp
  -- The proof proceeds by applying the continuity of f.
  apply tendsto_nhdsWithin_of_tendsto_nhds
  apply ContinuousAt.tendsto
  apply ContinuousOn.continuousAt (s := Set.Icc (a ⟨i + 1, hi⟩ - δ) (a ⟨i + 1, hi⟩ + δ))
  apply continuousOn_finset_sum
  · intro ⟨j, hasSum_le_inj⟩ hj_mem
    apply ContinuousOn.div
    · exact continuousOn_const
    · apply ContinuousOn.sub
      · exact continuousOn_const
      · apply continuousOn_id'
    · intro x hx
      by_cases hj : j ≥ i + 2
      · apply ne_of_gt
        simp
        apply lt_of_le_of_lt hx.2
        apply lt_of_lt_of_le (hadd_lt ?_)
        apply StrictMono.monotone ha
        exact hj
        apply lt_of_le_of_lt hj
        exact hasSum_le_inj
      · simp at hj hj_mem
        apply ne_of_lt
        simp
        apply lt_of_lt_of_le ?_ hx.1
        apply lt_of_le_of_lt ?_ hlt_sub
        apply StrictMono.monotone ha
        simp
        apply Nat.le_of_lt_succ
        apply lt_of_le_of_ne ?_ hj_mem
        exact Nat.le_of_lt_succ hj
  · simp
    exact hδpos

/- We show that for any i + 1 < n such that a_i > 0, there exists a root in (ai, a_{i+1}) -/
lemma exists_solution_of_pos {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a) (f : ℝ → ℝ) (hf : f = fun x => ∑ i : Fin n, a i / (a i - x)) {i : ℕ} (hi : i + 1 < n)
    (hai : a ⟨i, by exact Nat.lt_of_succ_lt hi⟩ > 0) :
    ∃ x ∈ Set.Ioo (a ⟨i, by exact Nat.lt_of_succ_lt hi⟩) (a ⟨i + 1, hi⟩), f x = n := by
  let s := Set.Ioo (a ⟨i, by exact Nat.lt_of_succ_lt hi⟩) (a ⟨i + 1, hi⟩)
  have hf₁ : f = fun x => ∑ j ∈ univ.erase ⟨i, Nat.lt_of_succ_lt hi⟩, a j / (a j - x) + a ⟨i, Nat.lt_of_succ_lt hi⟩ / (a ⟨i, Nat.lt_of_succ_lt hi⟩ - x) := by
    ext x
    simp [hf]
  have hf₂ : f = fun x => ∑ j ∈ univ.erase ⟨i + 1, hi⟩, a j / (a j - x) + a ⟨i + 1, hi⟩ / (a ⟨i + 1, hi⟩ - x) := by
    ext x
    simp [hf]
  -- Apply the intermediate value theorem.
  have himg_s : f '' s = Set.univ := by
    apply le_antisymm
    · simp
    · have : (nhdsWithin (a ⟨i, Nat.lt_of_succ_lt hi⟩) s).NeBot := by
        refine left_nhdsWithin_Ioo_neBot ?_
        apply ha
        simp
      have : (nhdsWithin (a ⟨i + 1, hi⟩) s).NeBot := by
        refine right_nhdsWithin_Ioo_neBot ?_
        apply ha
        simp
      -- Note that in this case, if x → a i, fx → -∞.
      -- When x → a (i + 1), fx → +∞.
      apply IsPreconnected.intermediate_value_Iii (l₁ := nhdsWithin (a ⟨i, Nat.lt_of_succ_lt hi⟩) s) (l₂ := nhdsWithin (a ⟨i + 1, hi⟩) s)
      · exact isPreconnected_Ioo
      · simp
        exact self_mem_nhdsWithin
      · simp
        exact self_mem_nhdsWithin
      · apply continuousOn_f a ha f hf hi
      · rw [hf₁]
        apply Filter.Tendsto.add_atBot (C := ∑ j ∈ univ.erase ⟨i, Nat.lt_of_succ_lt hi⟩, a j / (a j - a ⟨i, Nat.lt_of_succ_lt hi⟩))
        · apply tendsTo_nhds a ha hi
        · exact tendsto_atBot_right_of_pos hai
      · rw [hf₂]
        apply Filter.Tendsto.add_atTop (C := ∑ j ∈ univ.erase ⟨i + 1, hi⟩, a j / (a j - a ⟨i + 1, hi⟩))
        · apply tendsTo_nhds_succ a ha hi
        · apply tendsto_atTop_left_of_pos
          apply lt_trans hai
          apply ha
          simp
  -- Therefore, we can find a root x such that f x = n ∈ (-∞, +∞).
  obtain ⟨x, hs, hf⟩ : ↑n ∈ f '' s  := by
    rw [himg_s]
    simp
  use x


/- We show that for any i + 1 < n such that a(i + 1) < 0, there exists a root in (ai, a_{i+1}) -/
lemma exists_solution_of_neg {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a) (f : ℝ → ℝ) (hf : f = fun x => ∑ i : Fin n, a i / (a i - x)) {i : ℕ} (hi : i + 1 < n)
    (hai : a ⟨i + 1, hi⟩ < 0) :
    ∃ x ∈ Set.Ioo (a ⟨i, by exact Nat.lt_of_succ_lt hi⟩) (a ⟨i + 1, hi⟩), f x = n := by
  let s := Set.Ioo (a ⟨i, by exact Nat.lt_of_succ_lt hi⟩) (a ⟨i + 1, hi⟩)
  have hf₁ : f = fun x => ∑ j ∈ univ.erase ⟨i, Nat.lt_of_succ_lt hi⟩, a j / (a j - x) + a ⟨i, Nat.lt_of_succ_lt hi⟩ / (a ⟨i, Nat.lt_of_succ_lt hi⟩ - x) := by
    ext x
    simp [hf]
  have hf₂ : f = fun x => ∑ j ∈ univ.erase ⟨i + 1, hi⟩, a j / (a j - x) + a ⟨i + 1, hi⟩ / (a ⟨i + 1, hi⟩ - x) := by
    ext x
    simp [hf]
  -- Apply the intermediate value theorem.
  have himg_s : f '' s = Set.univ := by
    apply le_antisymm
    · simp
    · have : (nhdsWithin (a ⟨i, Nat.lt_of_succ_lt hi⟩) s).NeBot := by
        refine left_nhdsWithin_Ioo_neBot ?_
        apply ha
        simp
      have : (nhdsWithin (a ⟨i + 1, hi⟩) s).NeBot := by
        refine right_nhdsWithin_Ioo_neBot ?_
        apply ha
        simp
      -- Note that in this case, if x → a (i + 1), fx → -∞.
      -- When x → a i, fx → +∞.
      apply IsPreconnected.intermediate_value_Iii (l₁ := nhdsWithin (a ⟨i + 1, hi⟩) s) (l₂ := nhdsWithin (a ⟨i, Nat.lt_of_succ_lt hi⟩) s)
      · exact isPreconnected_Ioo
      · simp
        exact self_mem_nhdsWithin
      · simp
        exact self_mem_nhdsWithin
      · apply continuousOn_f a ha f hf hi
      swap
      · rw [hf₁]
        apply Filter.Tendsto.add_atTop (C := ∑ j ∈ univ.erase ⟨i, Nat.lt_of_succ_lt hi⟩, a j / (a j - a ⟨i, Nat.lt_of_succ_lt hi⟩))
        · apply tendsTo_nhds a ha hi
        · apply tendsto_atTop_right_of_neg
          apply lt_trans ?_ hai
          apply ha
          simp
      · rw [hf₂]
        apply Filter.Tendsto.add_atBot (C := ∑ j ∈ univ.erase ⟨i + 1, hi⟩, a j / (a j - a ⟨i + 1, hi⟩))
        · apply tendsTo_nhds_succ a ha hi
        · apply tendsto_atBot_left_of_neg hai
  -- Therefore, we can find a root x such that f x = n ∈ (-∞, +∞).
  obtain ⟨x, hs, hf⟩ : ↑n ∈ f '' s  := by
    rw [himg_s]
    simp
  use x


/- We prove that for any i + 1 < n, there exists a root in (a_i, a_{i+1}). -/
lemma exists_solution {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a) (ha_ne : ∀ i, a i ≠ 0) (f : ℝ → ℝ) (hf : f = fun x => ∑ i : Fin n, a i / (a i - x)) {i : ℕ} (hi : i + 1 < n) :
    ∃ x ∈ Set.Ioo (a ⟨i, by exact Nat.lt_of_succ_lt hi⟩) (a ⟨i + 1, hi⟩), f x = n := by
  by_cases hai : a ⟨i + 1, hi⟩ < 0
  · -- If a_{i+1} < 0, we can find a solution in (a_i, a_{i+1}) by `exists_solution_of_neg`.
    exact exists_solution_of_neg a ha f hf hi hai
  by_cases hai' : a ⟨i, Nat.lt_of_succ_lt hi⟩ > 0
  · -- If a_i > 0, we can find a solution in (a_i, a_{i+1}) by `exists_solution_of_pos`.
    exact exists_solution_of_pos a ha f hf hi hai'
  · -- Otherwise, we have a i < 0 < a_{i+1} since ∀ i, a i ≠ 0.
    simp at hai hai'
    use 0
    simp
    -- Then 0 is such a root.
    split_ands
    · apply lt_of_le_of_ne hai'
      apply ha_ne
    · apply lt_of_le_of_ne hai
      rw [ne_comm]
      apply ha_ne
    · simp [hf]
      trans ∑ i : Fin n, 1
      · congr
        ext x
        exact (div_eq_one_iff_eq (ha_ne x)).mpr rfl
      · simp

/- 6. (HUN 1) If $a_{i}(i=1,2, \ldots, n)$ are distinct non-zero real numbers,
prove that the equation  $$ \frac{a_{1}}{a_{1}-x}+\frac{a_{2}}{a_{2}-x}+\cdots+\frac{a_{n}}{a_{n}-x}=n $$
has at least $n-1$ real roots. -/
theorem algebra_24819 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : (List.ofFn a).Nodup) (ha_ne : ∀ i, a i ≠ 0)
    (f : ℝ → ℝ) (hf : f = fun x => ∑ i : Fin n, a i / (a i - x)) : {x | x ∉ univ.image a ∧  f x = n}.encard ≥ n - 1 := by

  -- a is in fact an injective function.
  have ha_inj : Function.Injective a := by
    exact List.nodup_ofFn.mp ha

  -- wlog, we can assume that a is a strict monotone function.
  wlog hmono : StrictMono a generalizing a f with H
  · -- Otherwise, we can obtain a isomorphism σ : Fin n ≃ Fin n such that a ∘ ⇑σ is strict monotone.
    let img := univ.image a
    have hcard : img.card = n := by
      rw [card_image_of_injective _ ha_inj]
      simp
    let a' (i : Fin n) : img := ⟨a i, by simp [img]⟩
    have ha' : Function.Bijective a' := by
      apply Nat.bijective_iff_injective_and_card _ |>.mpr
      constructor
      · intro i j hij
        simp [a'] at hij
        exact ha_inj hij
      · simp [hcard]
    let φ : Fin n ≃ img := by apply Equiv.ofBijective a' ha'
    have hφ {x : img} : a (φ.symm x) = x := by
      have {i : Fin n} : a i = φ i := by simp [φ]
      rw [this]
      simp only [apply_symm_apply]
    obtain ⟨g, hiso⟩ := orderIsoOfFin img hcard
    have hg_mono : StrictMono g := by
      apply Monotone.strictMono_of_injective
      · intro a b hab
        apply hiso.mpr hab
      · exact Equiv.injective g
    let σ : Fin n ≃ Fin n := Equiv.trans g (Equiv.symm φ)
    have hσ : StrictMono (a ∘ ⇑σ) := by
      intro i j hij
      simp [σ]
      rw [hφ, hφ]
      simp
      apply hg_mono hij
    -- Note that a ∘ ⇑σ is injective, pariwise non-zero, and distinct.
    have hσ_inj : Function.Injective (a ∘ ⇑σ) := by
      exact (injective_comp σ a).mpr ha_inj
    have hσ_nodup : (List.ofFn (a ∘ ⇑σ)).Nodup := by
      exact List.nodup_ofFn_ofInjective hσ_inj
    have hσ_ne : ∀ i, (a ∘ ⇑σ) i ≠ 0 := by
      simp
      intro i
      apply ha_ne
    -- Moreover, we have f x = ∑ i : Fin n, (a ∘ ⇑σ) i / ((a ∘ ⇑σ) i - x).
    have hf' : f = fun x => ∑ i : Fin n, (a ∘ ⇑σ) i / ((a ∘ ⇑σ) i - x) := by
      ext x
      simp [hf]
      have : univ = univ.image σ := by
        exact Eq.symm (image_univ_equiv σ)
      nth_rw 1 [this, sum_image]
      intro x _ y _ h
      apply Equiv.injective σ h
    -- Therefore, by the hypothesis, we have {x | f x = n}.ncard ≥ n - 1.
    obtain H := H (a ∘ ⇑σ) hσ_nodup hσ_ne f hf' hσ_inj hσ
    have : univ.image (a ∘ ⇑σ) = univ.image a := by
      ext x
      simp
      constructor <;> intro h
      · obtain ⟨i, hi⟩ := h
        use σ i
      · obtain ⟨i, hi⟩ := h
        use σ.symm i
        simp [hi]
    rw [this] at H
    exact H
  · -- We have proved a lemma that if i + 1 < n, then there exists a solution x ∈ (a_i, a_(i + 1)) such that f x = n.
    let root (i : Fin (n - 1)) := (exists_solution a hmono ha_ne f hf (i := i) (by apply Nat.add_lt_of_lt_sub i.2)).choose
    have hroot_property (i : Fin (n - 1)) : root i ∈ Set.Ioo (a ⟨i, by exact Nat.lt_of_succ_lt (Nat.add_lt_of_lt_sub i.2)⟩) (a ⟨i + 1, Nat.add_lt_of_lt_sub i.2⟩) ∧ f (root i) = n := by
      exact (exists_solution a hmono ha_ne f hf (i := i) (by apply Nat.add_lt_of_lt_sub i.2)).choose_spec
    -- Take all such roots for i = 0, 1, ..., n - 2, and we obtain a set of roots.
    let rootSet := univ.image root
    -- Obviously, the roots are the roots of the equation f x = n.
    have hsub : ↑rootSet ⊆ {x | x ∉ univ.image a ∧ f x = n} := by
      intro x hx
      simp [rootSet] at hx
      obtain ⟨i, hi⟩ := hx
      obtain hroot := hroot_property i
      rw [hi] at hroot
      simp [hroot.2]
      intro ⟨j, hj⟩
      by_cases h : j ≥ i + 1
      · apply ne_of_gt
        apply lt_of_lt_of_le hroot.1.2
        apply StrictMono.monotone hmono
        simp
        exact h
      · simp at h
        apply ne_of_lt
        apply lt_of_le_of_lt ?_ hroot.1.1
        apply StrictMono.monotone hmono
        simp
        exact Nat.le_of_lt_succ h
    -- Then we know that the number of roots is at least the cardinality of the rootSet.
    have encard_le_encard {s t : Set ℝ} (h : s ⊆ t) : s.encard ≤ t.encard := by
      rw [←Set.union_diff_cancel h, Set.encard_union_eq Set.disjoint_sdiff_right]; exact le_self_add
    apply encard_le_encard at hsub
    apply le_trans ?_ hsub
    rw [Set.encard_eq_coe_toFinset_card]
    norm_cast
    simp
    rw [card_image_of_injective]
    · -- If all the roots are distinct, then there are at least n - 1 roots.
      simp
      rw [Nat.sub_add_cancel hn]
    · -- Therefore, we show that the roots are distinct.
      intro x y h
      by_contra h'
      -- However, the root obtained by x and y are in interval (a_x, a_(x + 1)) and (a_y, a_(y + 1)), respectively.
      -- wlog, assume that x < y.
      rcases lt_or_gt_of_ne h' with h' | h'
      · -- We have root x < a_(x + 1) ≤ a_y < root y.
        have : root x < root y := by
          obtain h₁ := hroot_property x
          obtain h₂ := hroot_property y
          simp at h₁ h₂
          apply lt_trans h₁.1.2
          apply lt_of_le_of_lt ?_ h₂.1.1
          apply StrictMono.monotone hmono
          simp
          exact h'
        simp [h] at this
      · have : root x > root y := by
          obtain h₁ := hroot_property x
          obtain h₂ := hroot_property y
          simp at h₁ h₂
          apply lt_trans h₂.1.2
          apply lt_of_le_of_lt ?_ h₁.1.1
          apply StrictMono.monotone hmono
          simp
          exact h'
        simp [h] at this
