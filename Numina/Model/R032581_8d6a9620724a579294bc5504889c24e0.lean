import Mathlib

theorem algebra_104412 {f : ℝ → ℝ} (h : ∀ x y, f (f (x * y)) = abs x * f y + 3 * f (x * y)) :
    (∀ x, f x = 0) ∨ (∀ x, f x = 4 * abs x) ∨ (∀ x, f x = -4 * abs x) := by 
  have h2 : ∀ y : ℝ, f (f y) = 4 * f y := by 
    intro y 
    specialize h 1 y 
    norm_num [abs_one] at h 
    linarith 
  have eq3 : f 0 = 0 := by
    have eq4 := h 0 0
    have eq5 := h 1 0
    simp [abs_zero, mul_zero, abs_one] at eq4 eq5
    linarith
  -- Now with `eq3 : f 0 = 0` proven, we can make further progress.
  have eq4 : f (f 0) = 0 := by
    rw [show f 0 = (0 : ℝ) by linarith] 
    all_goals 
      norm_num [eq3, h2] 
  have h3 : ∀ x : ℝ, f x = f 1 * abs x := by
    intro x 
    specialize h x 1 
    norm_num [abs_one] at h 
    have eq4 : f (f x) = 4 * f x := by 
      specialize h2 x 
      simpa using h2 
    linarith [h, eq4]
  have h5 : f 1 * abs (f 1) = 4 * f 1 := by 
    have eqf1 := h2 1 
    have eqf1' : f (f 1) = f 1 * abs (f 1) := by 
      specialize h3 (f 1) 
      simpa using h3 
    linarith [eqf1, eqf1']
  -- Now from `h5 f1 * |f1| =4 * f1`.
  have h6 : f 1 = 0 ∨ (f 1 = 4 ∨ f 1 = -4) := by 
    by_cases h7 : f 1 = 0 
    · 
      left 
      exact h7 
    · -- case f 1 ≠ 0 
      have h8 : abs (f 1) = 4 := by 
        apply (mul_left_inj' h7).mp 
        linarith 
      have h77 : f 1 = 4 ∨ f 1 = -4 := by 
        cases eq_or_eq_neg_of_abs_eq h8 with 
        | inl h9 => 
          left 
          linarith 
        | inr h10 => 
          right 
          linarith 
      right 
      tauto 
  cases h6 with 
  | inl hf1 => 
    left 
    intro x 
    specialize h3 x 
    rw [hf1] at h3 
    linarith 
  | inr h6 => 
    have h7 : f 1 = 4 ∨ f 1 = -4 := h6 
    cases h7 with 
    | inl hf1 => 
      right 
      left 
      intro x 
      specialize h3 x 
      rw [hf1] at h3 
      linarith 
    | inr hf1 => 
      right 
      right 
      intro x 
      specialize h3 x 
      rw [hf1] at h3 
      linarith