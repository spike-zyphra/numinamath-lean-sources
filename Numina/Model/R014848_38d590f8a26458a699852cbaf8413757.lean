import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12343 (a : ℝ) :
  {y | ∃ x, y = logb 2016 (x^2 - a * x + 65)} ⊆ Ioi 0 ↔ a ∈ Ioo (-16) 16 := by
  constructor
  · -- Assume that the range is a subset of R^+, prove that -16 < a < 16.
    intro h
    have h1 : -16 < a := by
      by_contra ha
      push_neg at ha
      have h2 : a ≤ -16 := by linarith
      have h3 : a ^ 2 ≥ 256 := by nlinarith
      have h4 : ∃ x, x ^ 2 - a * x + 64 = 0 := by
        use (a - Real.sqrt (a^2 - 256)) / 2
        nlinarith [Real.sqrt_nonneg (a^2 - 256), Real.sq_sqrt (show 0 ≤ a ^ 2 - 256 by nlinarith)]
      rcases h4 with ⟨x, hx⟩
      have hx2 : x ^ 2 - a * x + 65 = 1 := by
        nlinarith
      have hx3 : logb 2016 (x ^ 2 - a * x + 65) = 0 := by
        rw [hx2]
        norm_num [logb_one]
      have h5 : logb 2016 (x ^ 2 - a * x + 65) > 0 := by 
        have h6 : logb 2016 (x ^ 2 - a * x + 65) ∈ Ioi 0 := by
          apply h
          use x
        simpa using h6
      linarith [hx3, h5]
    have h2 : a < 16 := by 
      by_contra ha
      push_neg at ha
      have h2 : a ≥ 16 := by linarith
      have h3 : a ^ 2 ≥ 256 := by nlinarith
      have h4 : ∃ x, x ^ 2 - a * x + 64 = 0 := by 
        use (a + Real.sqrt (a^2 - 256)) / 2
        nlinarith [Real.sqrt_nonneg (a^2 - 256), Real.sq_sqrt (show 0 ≤ a ^ 2 - 256 by nlinarith)]
      rcases h4 with ⟨x, hx⟩
      have hx2 : x ^ 2 - a * x + 65 = 1 := by 
        nlinarith
      have hx3 : logb 2016 (x ^ 2 - a * x + 65) = 0 := by
        rw [hx2]
        norm_num [logb_one]
      have h5 : logb 2016 (x ^ 2 - a * x + 65) > 0 := by 
        have h6 : logb 2016 (x ^ 2 - a * x + 65) ∈ Ioi 0 := by
          apply h
          use x
        simpa using h6
      linarith [hx3, h5]
    exact ⟨h1, h2⟩
  · -- Assume a ∈ (-16, 16), prove that the range is a subset of R^+.
    rintro ⟨ha1, ha2⟩
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx]
    have hx2 : x ^ 2 - a * x + 65 > 1 := by
      nlinarith [sq_nonneg (x - a / 2), sq_nonneg (a), sq_nonneg (x - 4), sq_nonneg (x + 4), sq_nonneg (a), sq_nonneg (a - 0), sq_nonneg (x - 16), sq_nonneg (x + 16)]
    have hx4 : logb 2016 (x ^ 2 - a * x + 65) > (0 : ℝ) := by 
      have h5 : x ^ 2 - a * x + 65 > (1 : ℝ) := hx2
      have h6 : logb 2016 (x ^ 2 - a * x + 65) > logb 2016 (1 : ℝ) := by
        apply Real.logb_lt_logb
        all_goals linarith
      have h7 : logb 2016 (1 : ℝ) = 0 := by 
        simp [logb_one]
      linarith [h7, h6]
    simpa using hx4