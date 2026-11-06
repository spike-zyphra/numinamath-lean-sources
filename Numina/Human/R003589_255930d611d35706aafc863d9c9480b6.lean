import Mathlib

theorem algebra_199173 (t : ℝ):
  {x : ℝ | x^3 - 3 * x = t}.encard = 1 ↔ 2 < |t| := by

  let f : ℝ → ℝ := fun x => x^3 - 3 * x

  have h_f_cont : Continuous f := by continuity

  have h_f_mono1 : StrictMonoOn f (Set.Iic (-1)) := by
    intro x hx y hy hxy
    unfold f
    simp at hx hy
    nlinarith [
      sq_nonneg (x + y + 2),  
      mul_nonneg (show (0 : ℝ) ≤ (x + 1) ^ 2 by positivity) (show (0 : ℝ) ≤ (y + 1) ^ 2 by positivity)
    ]

  have h_f_mono2 : StrictAntiOn f (Set.Icc (-1) 1) := by
    intro x hx y hy hxy
    unfold f
    simp at hx hy
    have ⟨hx1, hx2⟩ := hx
    have ⟨hy1, hy2⟩ := hy
    nlinarith [
      sq_pos_of_pos (show (0 : ℝ) < y - x by linarith), 
      mul_pos (show (0 : ℝ) < y - x by linarith) (show (0 : ℝ) < (3 - (x^2 + x * y + y^2)) by nlinarith)
    ]
  
  have h_f_mono3 : StrictMonoOn f (Set.Ici 1) := by
    intro x hx y hy hxy
    unfold f
    simp at hx hy
    nlinarith [
      sq_nonneg (x - y), sq_nonneg (x + y - 2), 
      mul_nonneg (show (0 : ℝ) ≤ (x ^ 2 - 1) by nlinarith) (show (0 : ℝ) ≤ (y ^ 2 - 1) by nlinarith)
    ]

  constructor
  . intro h
    by_contra ht
    simp at ht

    have ht1 : t ∈ Set.Icc (-2) 2 := by
      rw [abs_le] at ht
      exact ht

    have ⟨h_f_at_neg_2, h_f_at_neg_1, h_f_at_1, h_f_at_2⟩ : 
      f (-2) = -2 ∧ f (-1) = 2 ∧ f 1 = -2 ∧ f 2 = 2 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals unfold f; ring

    have hx1: ∃ x, (-2 ≤ x ∧ x ≤ -1) ∧ f x = t := by
      have hab : -2 ≤ (-1:ℝ) := by linarith
      have hf : ContinuousOn f (Set.Icc (-2) (-1)) := Continuous.continuousOn h_f_cont
      have := intermediate_value_Icc hab hf
      rw [h_f_at_neg_2, h_f_at_neg_1, Set.subset_def] at this
      exact this t ht1

    have hx2: ∃ x, (1 ≤ x ∧ x ≤ 2) ∧ f x = t := by
      have hab : 1 ≤ (2:ℝ) := by linarith
      have hf : ContinuousOn f (Set.Icc 1 2) := Continuous.continuousOn h_f_cont
      have := intermediate_value_Icc hab hf
      rw [h_f_at_1, h_f_at_2, Set.subset_def] at this
      exact this t ht1

    rcases hx1 with ⟨x1, hx1⟩
    rcases hx2 with ⟨x2, hx2⟩
    have hx12 : x1 ≠ x2 := by linarith
    have : {x1, x2} ⊆ {x : ℝ | x^3 - 3 * x = t} := by
      intro x hx
      rcases hx with rfl | rfl
      . simp
        exact hx1.2
      . simp
        exact hx2.2
    
    apply Set.encard_mono at this
    rw [h] at this
    rw [Set.encard_pair hx12] at this
    norm_num at this

  . intro ht
    rw [lt_abs] at ht
    rcases ht with h | h
    . have ht1 : t ∈ Set.Icc (f 1) (f t) := by
        unfold f
        simp
        refine ⟨by linarith, ?_⟩
        suffices t*(2-t)*(2+t) ≤ 0 by linarith
        rw [mul_nonpos_iff]; right
        refine ⟨?_, by linarith⟩
        rw [mul_nonpos_iff]; left
        constructor <;> linarith

      have : ∃! x0, x0^3 - 3 * x0 = t := by
        have hab : 1 ≤ t := by linarith
        have hf : ContinuousOn f (Set.Icc 1 t) := Continuous.continuousOn h_f_cont
        have := intermediate_value_Icc hab hf
        rw [Set.subset_def] at this
        have := this t ht1
        simp at this
        obtain ⟨x0, ⟨hx1, hx2⟩, hx3⟩ := this
        use x0
        constructor
        . simp
          exact hx3
        . intro y hy
          by_cases hy1 : y ≤ 1
          . suffices f y ≤ f (-1) by
              unfold f at this
              rw [hy] at this
              linarith

            rcases lt_trichotomy y (-1) with hy2 | rfl | hy2
            . have := @h_f_mono1 y (by simp; linarith)
              have := @this (-1)
              simp at this
              have := this hy2
              linarith
            . rfl
            . have := @h_f_mono2 (-1) (by simp)
              have := @this y (by simp; constructor <;> linarith) hy2
              linarith
          . simp at hy1
            have h_f_inj : Set.InjOn f (Set.Ici 1) := StrictMonoOn.injOn h_f_mono3
            have hy2 : y ∈ Set.Ici 1 := by simp; linarith
            have hx0 : x0 ∈ Set.Ici 1 := by simp; linarith
            have : f y = f x0 := by rw [hx3, ← hy]
            apply h_f_inj hy2 hx0 at this
            exact this

      rcases this with ⟨x0, hx0, hy⟩
      suffices {x : ℝ | x^3 - 3 * x = t} = {x0} by
        rw [this]
        simp
      ext x
      simp
      constructor
      . intro hx
        have := hy x
        simp at this
        exact this hx
      . intro hx
        rw [hx]
        exact hx0
    . have ht1 : t ∈ Set.Icc (f t) (f (-1)) := by
        unfold f
        simp
        refine ⟨?_, by linarith⟩
        suffices t*(t-2)*(2+t) ≤ 0 by linarith
        rw [mul_nonpos_iff]; left
        refine ⟨?_, by linarith⟩
        rw [mul_nonneg_iff]; right
        constructor <;> linarith

      have : ∃! x0, x0^3 - 3 * x0 = t := by
        have hab : t ≤ -1 := by linarith
        have hf : ContinuousOn f (Set.Icc t (-1)) := Continuous.continuousOn h_f_cont
        have := intermediate_value_Icc hab hf
        rw [Set.subset_def] at this
        have := this t ht1
        simp at this
        obtain ⟨x0, ⟨hx1, hx2⟩, hx3⟩ := this
        use x0
        constructor
        . simp
          exact hx3
        . intro y hy
          by_cases hy1 : y < -1
          . have h_f_inj : Set.InjOn f (Set.Iic (-1)) := StrictMonoOn.injOn h_f_mono1
            have hy2 : y ∈ Set.Iic (-1) := by simp; linarith
            have hx0 : x0 ∈ Set.Iic (-1) := by simp; linarith
            have : f y = f x0 := by rw [hx3, ← hy]
            apply h_f_inj hy2 hx0 at this
            exact this
          . simp at hy1
            suffices f 1 ≤ f y by
              unfold f at this
              rw [hy] at this
              linarith

            rcases lt_trichotomy y 1 with hy2 | rfl | hy2
            . have := @h_f_mono2 y (by simp; constructor <;> linarith)
              have := @this 1 (by simp) hy2
              linarith
            . rfl
            . have := @h_f_mono3 1 (by simp)
              have := @this y (by simp; linarith) hy2
              linarith
      rcases this with ⟨x0, hx0, hy⟩
      suffices {x : ℝ | x^3 - 3 * x = t} = {x0} by
        rw [this]
        simp
      ext x
      simp
      constructor
      . intro hx
        have := hy x
        simp at this
        exact this hx
      . intro hx
        rw [hx]
        exact hx0
