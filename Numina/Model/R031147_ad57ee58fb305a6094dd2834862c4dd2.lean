import Mathlib

  theorem algebra_108425 (a d : ℝ) 
  (h₅ : (a ^ 2 + (a + d) ^ 2 + (a + 2 * d) ^ 2 + (a + 3 * d) ^ 2) =
  (a * (a + d) * (a + 2 * d))) (h₆ : (a ^ 2 + (a + d) ^ 2 + (a + 2 * d) ^ 2 +
  (a + 3 * d) ^ 2) = (a + 4 * d) * (a + 5 * d)) :
   (a = d ∧ (d = 0 ∨ d = 5)) ∨ (a = (-2)*d ∧ d = 0):= by
  -- From h6 expanding the equations
  have h8 : a ^ 2 + a * d - 2 * d ^ 2 = 0 := by 
    nlinarith
  -- Factorize the quadratic expression in h8
  have h7 : (a + 2 * d) * (a - d) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h7) with
  | inl h9 =>
    -- Case 1: a + 2d = 0
    have h10 : a = -2 * d := by linarith 
    have h70 : d = 0 := by
      rw [show a = -2 * d by linarith] at h₅
      nlinarith [sq_nonneg (d ^ 2), sq_nonneg (d - 0)]
    right
    exact ⟨by linarith, by linarith⟩ 
  | inr h9 =>
    -- Case 2: a - d = 0
    have h14 : a = d := by nlinarith 
    have h80 : d ^ 2 * (d - 5) = 0 := by
      rw [show a = d by linarith] at h₅ 
      nlinarith 
    cases (mul_eq_zero.mp h80) with
    | inl h1 => 
      have h5 : d = 0 := by
        nlinarith 
      have ha : a = 0 := by 
        nlinarith
      left 
      simp [ha, h5] 
    | inr h2 => 
      have h19 : d = 5 := by 
        nlinarith 
      have ha : a = 5 := by 
        nlinarith 
      left 
      simp [ha, h19]
      all_goals 
      nlinarith