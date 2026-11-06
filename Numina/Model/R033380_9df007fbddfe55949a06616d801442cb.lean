import Mathlib

theorem algebra_323297 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n > 0, a (n + 1) = 1 + a n + Real.sqrt (1 + 4 * a n)) :
    ∀ n > 0, a n = 1 + (n - 1) * (n + Real.sqrt 5 - 1) := by
  intro n hn
  have h1 : ∀ (n : ℕ), n > 0 → a n = 1 + (n - 1) * (n + Real.sqrt 5 - 1) := by
    intro n hn
    induction n with
    | zero => linarith
    | succ n ih =>
      cases n with
      | zero => 
        rw [ha1]
        norm_num
        all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by nlinarith)]
      | succ n =>
        have h2 := ih (by linarith)
        have h3 : a ((n + 1) + 1) = 1 + a (n + 1) + Real.sqrt (1 + 4 * a (n + 1)) := by
          specialize han (n + 1) (by linarith)
          simpa using han
        rw [h3, h2]
        simp [Real.sqrt_nonneg, pow_two] at *
        ring_nf
        have h4 : Real.sqrt (5 + ↑n * Real.sqrt 5 * 4 + ↑n ^ 2 * 4) = Real.sqrt 5 + 2 * (↑n : ℝ) := by
          have h5 : (Real.sqrt 5 + 2 * (↑n : ℝ)) ^ 2 = (5 + ↑n * Real.sqrt 5 * 4 + ↑n ^ 2 * 4 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (↑n : ℝ), mul_nonneg (Real.sqrt_nonneg 5) (show (0 : ℝ) ≤ (↑n : ℝ) by positivity)]
          have h6 : Real.sqrt 5 + 2 * (↑n : ℝ) ≥ 0 := by
            positivity
          have h7 : Real.sqrt (5 + ↑n * Real.sqrt 5 * 4 + ↑n ^ 2 * 4) = Real.sqrt 5 + 2 * (↑n : ℝ) := by
            rw [← h5]
            field_simp [Real.sqrt_sq (show (0 : ℝ) ≤ Real.sqrt 5 + 2 * ↑n by positivity)]
          exact h7
        rw [h4]
        all_goals 
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (↑n : ℝ), mul_nonneg (Real.sqrt_nonneg 5) (show (0 : ℝ) ≤ (↑n : ℝ) by positivity)]
  apply h1 n hn