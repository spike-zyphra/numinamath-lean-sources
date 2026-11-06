import Mathlib

theorem algebra_15054 :
    IsGreatest {a | (7 * √((2 * a) ^ 2 + 1) - 4 * a ^ 2 - 1) / (√(1 + 4 * a ^ 2) + 3) = 2} √2 := by
  constructor
  · -- First, show that √2 is indeed in the set.
    have h1 : (7 * √((2 * √2) ^ 2 + 1) - 4 * √2 ^ 2 - 1) / (√(1 + 4 * √2 ^ 2) + 3) = 2 := by
      have h2 : √((2 * √2) ^ 2 + 1) = 3 := by
        have h3 : (2 * √2) ^ 2 + 1 = (9 : ℝ) := by
          calc
            (2 * √2) ^ 2 + 1 = 4 * (√2 ^ 2) + 1 := by ring
            _ = 4 * (2 : ℝ) + 1 := by rw [Real.sq_sqrt]; positivity
            _ = 8 + 1 := by norm_num
            _ = (9 : ℝ) := by norm_num
        rw [h3]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h4 : √(1 + 4 * √2 ^ 2) = 3 := by
        have h5 : 1 + 4 * √2 ^ 2 = (9 : ℝ) := by
          calc
            1 + 4 * √2 ^ 2 = 1 + 4 * (2 : ℝ) := by rw [Real.sq_sqrt]; positivity
            _ = 1 + 8 := by norm_num
            _ = (9 : ℝ) := by norm_num
        rw [h5]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2, h4]
      have h6 : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      rw [h6]
      norm_num
    simp_all
  · -- Now, prove that √2 is the greatest.
    intro a ha
    simp at ha
    have h2 : (7 * √((2 * a) ^ 2 + 1) - 4 * a ^ 2 - 1) / (√(1 + 4 * a ^ 2) + 3) = 2 := by
      simpa using ha
    have h5 : √((2 * a) ^ 2 + 1) = √(1 + 4 * a ^ 2) := by
      ring_nf
    rw [h5] at h2
    have h6 : √(1 + 4 * a ^ 2) + 3 ≠ 0 := by
      positivity
    have eq1 : 7 * √(1 + 4 * a ^ 2) - 4 * a ^ 2 - 1 = 2 * (√(1 + 4 * a ^ 2) + 3) := by
      field_simp [h6] at h2 ⊢
      linarith
    have eq2 : 7 * √(1 + 4 * a ^ 2) - 2 * √(1 + 4 * a ^ 2) = 4 * a ^ 2 + 7 := by
      linarith [eq1]
    have eq3 : 5 * √(1 + 4 * a ^ 2) = 4 * a ^ 2 + 7 := by
      nlinarith [eq2]
    have eq4 : 25 * (1 + 4 * a ^ 2) = (4 * a ^ 2 + 7) ^ 2 := by
      have h7 : (√(1 + 4 * a ^ 2)) ^ 2 = 1 + 4 * a ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith [show 0 ≤ (1 + 4 * a ^ 2 : ℝ) by nlinarith]
      have h8 : (4 * a ^ 2 + 7 : ℝ) ^ 2 = (4 * a ^ 2 + 7) ^ 2 := by rfl
      nlinarith [h7, sq_nonneg (√(1 + 4 * a ^ 2) - (4 * a ^ 2 + 7) / 5)]
    have eq5 : (a ^ 2 - 2) * (a ^ 2 - 3 / 4) = 0 := by
      nlinarith [eq4]
    cases' (mul_eq_zero.mp eq5) with h8 h9
    · -- Case $a^2 - 2 = 0$, so $a^2 = 2$, so $a \leq \sqrt{2}$.
      have ha2 : a ^ 2 = 2 := by linarith
      nlinarith [Real.sqrt_nonneg 2, show (√2) ^ 2 = 2 by norm_num, sq_nonneg (a - √2)]
    · -- Case $a^2 - 3/4 = 0$, so $a^2 = 3/4$, so $a \leq \sqrt{2}$.
      have ha2 : a ^ 2 = 3 / 4 := by linarith
      nlinarith [Real.sqrt_nonneg 2, show (√2) ^ 2 = 2 by norm_num, sq_nonneg (a - √2)]