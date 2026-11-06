import Mathlib

open Real Set

theorem algebra_318048 (m n p : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (h : m^2 + n^2 - p^2 = 0) :
    p / (m + n) ≥ sqrt 2 / 2 := by

  have h1 : p ^ 2 = m ^ 2 + n ^ 2 := by linarith

  have h2 : m + n > 0 := by nlinarith

  have h4 : p ^ 2 ≥ (1 / 2) * (m + n) ^ 2 := by
    nlinarith [sq_nonneg (m - n)]

  have h7 : p ≥ (Real.sqrt 2 / 2) * (m + n) := by
    have h8 : ( (Real.sqrt 2 / 2) * (m + n) ) ^ 2 ≤ p ^ 2 := by
      have h9 : ( (Real.sqrt 2 / 2) * (m + n) ) ^ 2 = ( (Real.sqrt 2 / 2) ^ 2 ) * (m + n) ^ 2 := by ring
      rw [h9]
      have h10 : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
        calc
          (Real.sqrt 2 / 2) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
          _ = ( (Real.sqrt 2) ^ 2 ) / 4 := by ring
          _ = (2 : ℝ) / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          _ = (1 / 2 : ℝ) := by norm_num
      rw [h10]
      nlinarith [sq_nonneg (m - n)]
    have h9 : ( (Real.sqrt 2 / 2) * (m + n) ) ≤ p := by
      nlinarith [sq_nonneg (p - (Real.sqrt 2 / 2) * (m + n)), Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), sq_nonneg (m - n)]
    exact h9

  have h8 : p / (m + n) ≥ Real.sqrt 2 / 2 := by
    have h9 : 0 < m + n := by linarith
    have h10 : p ≥ (Real.sqrt 2 / 2) * (m + n) := by
      have h8 : ( (Real.sqrt 2 / 2) * (m + n) ) ^ 2 ≤ p ^ 2 := by
        have h9 : ( (Real.sqrt 2 / 2) * (m + n) ) ^ 2 = ( (Real.sqrt 2 / 2) ^ 2 ) * (m + n) ^ 2 := by ring
        rw [h9]
        have h10 : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
          calc
            (Real.sqrt 2 / 2) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
            _ = ( (Real.sqrt 2) ^ 2 ) / 4 := by ring
            _ = (2 : ℝ) / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            _ = (1 / 2 : ℝ) := by norm_num
        rw [h10]
        nlinarith [sq_nonneg (m - n)]
      have h9 : ( (Real.sqrt 2 / 2) * (m + n) ) ≤ p := by
        nlinarith [sq_nonneg (p - (Real.sqrt 2 / 2) * (m + n)), Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), sq_nonneg (m - n)]
      exact h9
    have h11 : p / (m + n) ≥ (Real.sqrt 2 / 2) * (m + n) / (m + n) := by
      apply (div_le_div_right h9).mpr
      nlinarith
    have h12 : (Real.sqrt 2 / 2) * (m + n) / (m + n) = Real.sqrt 2 / 2 := by
      field_simp [show m + n ≠ 0 by linarith]
      <;> nlinarith
    linarith [h12, h11]

  exact h8