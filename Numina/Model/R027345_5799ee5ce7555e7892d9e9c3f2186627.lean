import Mathlib

theorem algebra_21047 {A B P : ℝ × ℝ}
    (hA : A.1 = (7 + 3 * Real.sqrt 5) / 2 ∧ A.2 = Real.sqrt (4 * (7 + 3 * Real.sqrt 5) / 2))
    (hB : B.1 = (7 - 3 * Real.sqrt 5) / 2 ∧ B.2 = Real.sqrt (4 * (7 - 3 * Real.sqrt 5) / 2))
    (hP : P.1 = 1 ∧ P.2 = 3) :
    Real.sqrt ((A.1 - B.1)^2 + (A.2 - B.2)^2) = Real.sqrt 65 := by
  rcases hA with ⟨hx_A, hy_A⟩
  rcases hB with ⟨hx_B, hy_B⟩
  rcases hP with ⟨hx_P, hy_P⟩
  have ha2 : A.2 = 3 + Real.sqrt 5 := by
    have h1 : (4 * (7 + 3 * Real.sqrt 5) / 2 : ℝ) = (3 + Real.sqrt 5) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    have h2 : Real.sqrt (4 * (7 + 3 * Real.sqrt 5) / 2) = Real.sqrt ((3 + Real.sqrt 5) ^ 2) := by
      rw [h1]
    have h3 : Real.sqrt ((3 + Real.sqrt 5) ^ 2) = 3 + Real.sqrt 5 := by
      rw [Real.sqrt_sq]
      positivity
    rw [h2, h3] at hy_A
    linarith
  have hb2 : B.2 = 3 - Real.sqrt 5 := by
    have h1 : (4 * (7 - 3 * Real.sqrt 5) / 2 : ℝ) = (3 - Real.sqrt 5) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    have h2 : Real.sqrt (4 * (7 - 3 * Real.sqrt 5) / 2) = Real.sqrt ((3 - Real.sqrt 5) ^ 2) := by
      rw [h1]
    have h3 : Real.sqrt ((3 - Real.sqrt 5) ^ 2) = 3 - Real.sqrt 5 := by
      rw [Real.sqrt_sq]
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    rw [h2, h3] at hy_B
    linarith
  have h1 : (A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2 = (65 : ℝ) := by
    rw [show A.1 = (7 + 3 * Real.sqrt 5) / 2 by linarith [hx_A], show B.1 = (7 - 3 * Real.sqrt 5) / 2 by linarith [hx_B], ha2, hb2]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  have h2 : Real.sqrt ((A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2) = Real.sqrt (65 : ℝ) := by
    rw [h1]
  exact h2