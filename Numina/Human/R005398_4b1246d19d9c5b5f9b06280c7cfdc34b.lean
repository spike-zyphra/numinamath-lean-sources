import Mathlib

-- Consider the polynomial $P(x)=x^{3}+x^{2}-x+2$. Determine all real numbers $r$ for which there exists a complex number $z$ not in the reals such that $P(z)=r$.
theorem algebra_608137 (r : ℝ) (f : ℝ → ℝ)
  (hf : f = fun x => x^3 + x^2 - x + 2):
  {x | f x = r}.encard ≤ 1 ↔ r < 49/27 ∨ 3 < r := by

  -- Step 1: Prove continuity
  have h_f_cont : Continuous f := by
    rw [hf]
    continuity

  -- Step 2: Prove monotonicity on different intervals
  let x1 : ℝ := -1
  let x2 : ℝ := 1/3

  have h_f_mono1 : StrictMonoOn f (Set.Iic x1) := by
    intro x hx y hy hxy
    rw [hf]
    simp at hx hy ⊢
    unfold x1 at hx hy
    nlinarith [
      sq_nonneg (x + y + 2),
      mul_nonneg (show (0 : ℝ) ≤ (x + 1) ^ 2 by positivity) (show (0 : ℝ) ≤ (y + 1) ^ 2 by positivity)
    ]

  have h_f_mono2 : StrictAntiOn f (Set.Icc x1 x2) := by
    intro x hx y hy hxy
    rw [hf]
    simp at hx hy ⊢
    unfold x1 x2 at hx hy
    nlinarith [
      sq_pos_of_pos (show (0 : ℝ) < y - x by linarith),
      mul_pos (show (0 : ℝ) < y - x by linarith) (show (0 : ℝ) < (3 - (x^2 + x * y + y^2)) by nlinarith)
    ]

  have h_f_mono3 : StrictMonoOn f (Set.Ici x2) := by
    intro x hx y hy hxy
    rw [hf]
    simp at hx hy ⊢
    unfold x2 at hx hy
    nlinarith [
      sq_nonneg (x - y),
      mul_nonneg (show (0 : ℝ) ≤ (x - 1/3) by linarith) (show (0 : ℝ) ≤ (y - 1/3) by linarith)
    ]

  -- Step 3: Calculate critical values
  let y1 := f x1
  let y2 := f x2


  have ⟨h_y1, h_y2⟩: y1 = 3 ∧ y2 = 49/27 := by
    unfold y1 y2
    rw [hf]
    unfold x1 x2
    norm_num

  -- Step 4: Order the critical values
  have ⟨h_x1_lt_x2, h_y2_lt_y1⟩: x1 < x2 ∧ y2 < y1:= by
    unfold x1 x2
    rw [h_y1, h_y2]
    norm_num

  -- Step 5: Main proof by cases
  constructor
  -- Direction 1:
  · intro h_encard_le_1
    by_contra h_in_interval
    simp at h_in_interval
    -- Use intermediate value theorem to find multiple roots when r is outside the interval
    have : ∃ x0 x3, x0 ∈ Set.Iic x1 ∧ x3 ∈ Set.Ici x2 ∧ f x0 = r ∧ f x3 = r := by
      have hab : (-5/3 : ℝ) ≤ (-1 : ℝ) := by norm_num
      have hf_cont1 : ContinuousOn f (Set.Icc (-5/3) (-1)) := Continuous.continuousOn h_f_cont
      have := intermediate_value_Icc hab hf_cont1
      rw [Set.subset_def] at this
      have hr : r ∈ Set.Icc (f (-5/3)) (f (-1)) := by
        simp
        constructor
        all_goals
        . rw [hf]
          simp
          nlinarith
      have := this r hr
      obtain ⟨x0, ⟨hx0, hx0'⟩, hx0_eq⟩ := this

      have hab : (1/3 : ℝ) ≤ (1 : ℝ) := by norm_num
      have hf_cont2 : ContinuousOn f (Set.Icc (1/3) 1) := Continuous.continuousOn h_f_cont
      have := intermediate_value_Icc hab hf_cont2
      rw [Set.subset_def] at this
      have hr : r ∈ Set.Icc (f (1/3)) (f 1) := by
        simp
        constructor
        all_goals
        . rw [hf]
          simp
          nlinarith
      have := this r hr
      obtain ⟨x3, ⟨hx3, hx3'⟩, hx3_eq⟩ := this

      use x0, x3
      refine ⟨?_, by simp; exact hx3, hx0_eq, hx3_eq⟩
      simp
      unfold x1
      exact hx0'

    obtain ⟨x0, x3, hx0, hx3, hx0_eq, hx3_eq⟩ := this
    have : {x0, x3} ⊆ {x | f x = r} := by
      rintro x0 (rfl | rfl)
      . simp; exact hx0_eq
      . simp; exact hx3_eq
    apply Set.encard_mono at this
    have := le_trans this h_encard_le_1
    rw [Set.encard_pair (by simp at hx0 hx3; linarith)] at this
    norm_num at this

  -- Direction 2:
  · rintro (hr1 | hr2)
    . have hab : r - 4 ≤ x1 := by unfold x1; linarith
      have hf_cont : ContinuousOn f (Set.Icc (r - 4) x1) := Continuous.continuousOn h_f_cont
      have := intermediate_value_Icc hab hf_cont
      rw [Set.subset_def] at this
      have hr : r ∈ Set.Icc (f (r - 4)) (y1) := by
        simp
        constructor
        . rw [hf]
          simp
          nlinarith
        . rw [h_y1]
          linarith
      have := this r hr
      obtain ⟨x0, ⟨hx0, hx0'⟩, hx0_eq⟩ := this
      suffices {x | f x = r} ⊆ {x0} by
        apply Set.encard_mono at this
        simp at this
        exact this

      intro x3 hx3
      simp at hx3 ⊢
      by_cases hx3_lt : x3 < x1
      . have h_f_inj : Set.InjOn f (Set.Iic x1) := StrictMonoOn.injOn h_f_mono1
        have hy1 : x3 ∈ Set.Iic x1 := by simp; linarith
        have hx0 : x0 ∈ Set.Iic x1 := by simp; exact hx0'
        have : f x3 = f x0 := by rw [hx3, hx0_eq]
        apply h_f_inj hy1 hx0 at this
        exact this
      . suffices y2 ≤ f x3 by linarith
        rcases lt_trichotomy x3 x2 with h | rfl | h
        . have := @h_f_mono2 x3 (by simp; constructor <;> linarith) x2 (by simp; linarith) h
          linarith
        . rfl
        . have := @h_f_mono3 x2 (by simp) x3 (by simp; linarith) h
          linarith

    . have hab : x2 ≤ r := by unfold x2; linarith
      have hf_cont : ContinuousOn f (Set.Icc x2 r) := Continuous.continuousOn h_f_cont
      have := intermediate_value_Icc hab hf_cont
      rw [Set.subset_def] at this
      have hr : r ∈ Set.Icc y2 (f r) := by
        constructor
        . rw [h_y2]
          linarith
        . rw [hf]
          simp
          nlinarith
      have := this r hr
      obtain ⟨x0, ⟨hx0, hx0'⟩, hx0_eq⟩ := this
      suffices {x | f x = r} ⊆ {x0} by
        apply Set.encard_mono at this
        simp at this
        exact this

      intro x3 hx3
      simp at hx3 ⊢
      by_cases hx3_lt : x3 < x2
      . suffices f x3 ≤ y1 by linarith
        rcases lt_trichotomy x3 x1 with h | rfl | h
        . have := @h_f_mono1 x3 (by simp; linarith) x1 (by simp) h
          linarith
        . rfl
        . have := @h_f_mono2 x1 (by simp; linarith) x3 (by simp; constructor <;> linarith) h
          linarith

      . simp at hx3_lt
        have h_f_inj : Set.InjOn f (Set.Ici x2) := StrictMonoOn.injOn h_f_mono3
        have hy2 : x3 ∈ Set.Ici x2 := by simp; exact hx3_lt
        have hx0 : x0 ∈ Set.Ici x2 := by simp; exact hx0
        have : f x3 = f x0 := by rw [hx3, hx0_eq]
        apply h_f_inj hy2 hx0 at this
        exact this
