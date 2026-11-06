import Mathlib

open Real

theorem algebra_610860 :
  ∀ (a b : ℝ),
    -- The point (a,b) lies on the curve x²-(y-1)²=1
    (a^2 - (b - 1)^2 = 1 ∧
    -- The tangent line at (a,b) passes through (0,0)
    (∃ (m : ℝ), m > 0 ∧
      -- Slope of the tangent line at the point (a,b)
      2 * a - 2 * (b - 1) * m = 0  ∧
      -- Point-slope form of the line through (a,b) with slope m, passing through (0,0)
      0 = b - m * a))
    -- The value of sin⁻¹(a/b) equals π/4
    → arcsin (a / b) = π / 4 := by
  intro a b h
  rcases h with ⟨h1, ⟨m, hm1, hm2, hm3⟩⟩

  have hb1 : b = m * a := by linarith

  have h6 : a = (b - 1) * m := by
    nlinarith

  rw [hb1] at h6

  have eq1 : a = (m * a - 1) * m := by 
    nlinarith

  have eq2 : a * (1 - m ^ 2) = -m := by 
    nlinarith

  have eq3 : a ^ 2 - (b - 1) ^ 2 = 1 := by linarith [h1]

  rw [hb1] at eq3

  have eq4 : m ^ 2 = 2 := by
    nlinarith [sq_pos_of_pos hm1, sq_nonneg (a * (1 - m ^ 2)), sq_nonneg (a - m), sq_nonneg (a + m)]

  have eq5 : m ^ 2 = 2 := eq4
  have eq6 : a = m := by 
    rw [show 1 - m ^ 2 = -1 by nlinarith] at eq2
    nlinarith

  have eq7 : b = (2 : ℝ) := by
    nlinarith [sq_pos_of_pos hm1, eq5, eq6, hm1]

  have h11 : a / b = (Real.sqrt 2 : ℝ) / 2 := by
    have eq13 : a = (Real.sqrt 2 : ℝ) := by
      have eq14 : m ^ 2 = (2 : ℝ) := eq5
      have m_pos : m > 0 := hm1
      have eq15 : m = Real.sqrt (2 : ℝ) := by
        rw [← eq14]
        field_simp
      have : a = m := eq6
      rw [this, eq15]
    rw [eq13, eq7]
    all_goals field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h5 : arcsin (a / b) = arcsin (Real.sqrt 2 / 2) := by
    rw [h11]

  have h7 : arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
    have h8 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h9 : arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 := by
      apply arcsin_sin
      all_goals linarith [Real.pi_pos]
    rw [h8] at h9
    linarith

  linarith [h5, h7]