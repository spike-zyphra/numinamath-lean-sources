import Mathlib

theorem algebra_307863 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a = 2 ∧ b = Real.sqrt 2) :
    (Real.sqrt 2^2 / a^2 + 1^2 / b^2 = 1) ∧ ¬(∀ a b : ℝ, a ≠ 0 → b ≠ 0 →
    (Real.sqrt 2^2 / a^2 + 1^2 / b^2 = 1) → a = 2 ∧ b = Real.sqrt 2) := by
  rcases h with ⟨ha2, hb2⟩
  constructor
  · -- Show that with a=2 and b=√2, the equation holds
    rw [ha2, hb2]
    have h1 : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      linarith
    field_simp [h1]
    <;> nlinarith [Real.sqrt_nonneg 2]
  · -- Show that it's not necessary, by providing a counterexample
    intro h1
    have h2 := h1 (4 * Real.sqrt 2 / 3) (4 * Real.sqrt 7 / 7) 
      (by
        have h1 : Real.sqrt 2 > 0 := by positivity
        have h2 : Real.sqrt 2 ≠ 0 := by linarith
        have h3 : Real.sqrt 7 > 0 := by positivity
        have h4 : Real.sqrt 7 ≠ 0 := by linarith
        norm_num
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 7, 
          Real.sq_sqrt (show 2 ≥ 0 by norm_num), Real.sq_sqrt (show 7 ≥ 0 by norm_num)]
      ) (by
        have h1 : Real.sqrt 2 > 0 := by positivity
        have h2 : Real.sqrt 2 ≠ 0 := by linarith
        have h3 : Real.sqrt 7 > 0 := by positivity
        have h4 : Real.sqrt 7 ≠ 0 := by linarith
        norm_num
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 7, 
          Real.sq_sqrt (show 2 ≥ 0 by norm_num), Real.sq_sqrt (show 7 ≥ 0 by norm_num)]
      )
      (by
        have h1 : Real.sqrt 2 > 0 := by positivity
        have h2 : Real.sqrt 2 ≠ 0 := by linarith
        have h3 : Real.sqrt 7 > 0 := by positivity
        have h4 : Real.sqrt 7 ≠ 0 := by linarith
        field_simp [h2, h4, Real.sq_sqrt (show 2 ≥ 0 by norm_num), Real.sq_sqrt (show 7 ≥ 0 by norm_num)]
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 7, 
          sq_nonneg (Real.sqrt 2 * 3 - Real.sqrt 7 * 4), 
          sq_nonneg (Real.sqrt 2 * 7 - Real.sqrt 7 * 4 * Real.sqrt 2), 
          Real.sq_sqrt (show 2 ≥ 0 by norm_num), 
          Real.sq_sqrt (show 7 ≥ 0 by norm_num)]
      )
    norm_num [Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)] at h2
    all_goals nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 7, 
      Real.sq_sqrt (show 2 ≥ 0 by norm_num), Real.sq_sqrt (show 7 ≥ 0 by norm_num)]