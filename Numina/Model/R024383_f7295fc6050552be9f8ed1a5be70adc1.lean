import Mathlib

open BigOperators Real Set


theorem algebra_162906 {a : ℝ} (ha : a > 0)
  (x : ℝ → ℝ) (hx : ∀ t, x t = 5 * (t + 1)^2 + a / (t + 1)^5)
  (h : ∀ t ≥ 0, x t ≥ 24) :
  a ≥ 2 * sqrt ((24 / 7)^7) := by
  have h1 : x (Real.sqrt (24 / 7) - 1) ≥ 24 := by
    apply h
    have h2 : Real.sqrt (24 / 7) ≥ 1 := by
      have h3 : Real.sqrt (24 / 7) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
      have h4 : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one
      nlinarith
    nlinarith [Real.sqrt_nonneg (24 / 7)]
  have ht1 : x (Real.sqrt (24 / 7) - 1) = 5 * (Real.sqrt (24 / 7)) ^ 2 + a / (Real.sqrt (24 / 7) ) ^ 5 := by
    rw [hx]
    have ht2 : (Real.sqrt (24 / 7) - 1 + 1 : ℝ) = Real.sqrt (24 / 7) := by ring
    simp [ht2]
  rw [ht1] at h1
  have ht3 : (Real.sqrt (24 / 7) ) ^ 2 = (24 / 7 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have ht7 : a / (Real.sqrt (24 / 7) ) ^ 5 ≥ (48 / 7 : ℝ) := by
    have ht7 : 5 * (Real.sqrt (24 / 7)) ^ 2 + a / (Real.sqrt (24 / 7) ) ^ 5 ≥ (24 : ℝ) := by
      linarith
    rw [ht3] at ht7
    nlinarith
  have ht7' : a ≥ 48 / 7 * (Real.sqrt (24 / 7) ) ^ 5 := by
    have ht8 : a / (Real.sqrt (24 / 7) ) ^ 5 ≥ (48 / 7 : ℝ) := ht7
    have ht9 : (Real.sqrt (24 / 7) ) ^ 5 > 0 := by
      positivity
    have ht10 : a ≥ (48 / 7 : ℝ) * (Real.sqrt (24 / 7) ) ^ 5 := by
      apply (le_div_iff₀ ht9).mp at ht8
      linarith
    linarith
  have ht10 : 48 / 7 * (Real.sqrt (24 / 7) ) ^ 5 = 2 * (Real.sqrt (24 / 7) ) ^ 7 := by
    have ht11 : (Real.sqrt (24 / 7) ) ^ 7 = (Real.sqrt (24 / 7) ) ^ 5 * (Real.sqrt (24 / 7) ) ^ 2 := by ring
    rw [ht11, ht3]
    nlinarith
  have ht11 : a ≥ 2 * (Real.sqrt (24 / 7) ) ^ 7 := by
    nlinarith [ht7', ht10]
  have ht12 : 2 * sqrt ((24 / 7)^7) = 2 * (Real.sqrt (24 / 7) ) ^ 7 := by
    have ht18 : sqrt ((24 / 7 : ℝ) ^ 7) = (Real.sqrt (24 / 7) ) ^ 7 := by
      have ht23 : ((Real.sqrt (24 / 7 : ℝ)) ^ 7) ^ 2 = (24 / 7 : ℝ) ^ 7 := by
        calc
          ((Real.sqrt (24 / 7 : ℝ)) ^ 7) ^ 2 = (Real.sqrt (24 / 7 : ℝ) ^ 2) ^ 7 := by ring
          _ = (24 / 7 : ℝ) ^ 7 := by
            rw [Real.sq_sqrt (show (0 : ℝ) ≤ (24 / 7 : ℝ) by positivity)]
      have ht24 : (Real.sqrt (24 / 7 : ℝ)) ^ 7 ≥ 0 := by positivity
      have ht25 : Real.sqrt ((24 / 7 : ℝ) ^ 7) = (Real.sqrt (24 / 7 : ℝ)) ^ 7 := by
        have ht26 : Real.sqrt ((24 / 7 : ℝ) ^ 7) = Real.sqrt (( (Real.sqrt (24 / 7 : ℝ)) ^ 7 ) ^ 2) := by
          rw [ht23]
        have ht27 : Real.sqrt (( (Real.sqrt (24 / 7 : ℝ)) ^ 7 ) ^ 2) = (Real.sqrt (24 / 7 : ℝ)) ^ 7 := by
          rw [Real.sqrt_sq (show 0 ≤ (Real.sqrt (24 / 7 : ℝ)) ^ 7 by positivity)]
        rw [ht26, ht27]
      exact ht25
    linarith [ht18]
  linarith [ht11, ht12]