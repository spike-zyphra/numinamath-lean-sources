import Mathlib

theorem algebra_607240 :
    IsGreatest {r | ∃ x: ℝ, ∃ y: ℝ, ∃ z: ℝ, x + y + z = 2 ∧ x * y + y * z + z * x = 1 ∧ r = x - y } (2 / Real.sqrt 3) := by
  constructor
  · -- Show that 2/sqrt(3) is in the set.
    use (2 + Real.sqrt 3) / 3, (2 - Real.sqrt 3) / 3, 2 / 3
    constructor
    · -- Show that x+y+z=2
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    constructor
    · -- Show that x*y+y*z+z*x=1
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Show that 2 / Real.sqrt 3 = x - y
      have h3 : Real.sqrt 3 > 0 := by
        positivity
      have h4 : (2 + Real.sqrt 3) / 3 - (2 - Real.sqrt 3) / 3 = (2 * Real.sqrt 3) / 3 := by
        ring
      rw [h4]
      have h5 : 2 / Real.sqrt 3 = (2 * Real.sqrt 3) / 3 := by
        have h6 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        have h7 : Real.sqrt 3 ≠ 0 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        field_simp [h7]
        nlinarith [h6]
      linarith [h5]
  · -- Show that 2/sqrt(3) is the greatest element in the set
    intro r hr
    rcases hr with ⟨x, y, z, h1, h2, hr⟩
    have h3 : (x - y) ^ 2 ≤ 4 / 3 := by
      have eq1 : (x - y) ^ 2 = -3 * z ^ 2 + 4 * z := by
        have eq2 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
          nlinarith
        have eq3 : x + y = 2 - z := by linarith
        have eq4 : x * y = 1 - 2 * z + z ^ 2 := by
          have eq5 : x * y + y * z + z * x = 1 := h2
          have eq6 : x + y = 2 - z := by linarith
          have eq7 : x * y = 1 - z * (x + y) := by
            nlinarith
          rw [show x + y = 2 - z by linarith] at eq7
          nlinarith
        rw [eq2, eq3, eq4]
        nlinarith
      have eq2 : -3 * z ^ 2 + 4 * z ≤ 4 / 3 := by
        nlinarith [sq_nonneg (z - 2 / 3)]
      rw [eq1] at *
      linarith
    have h3' : (x - y) ≤ Real.sqrt (4 / 3) := by
      have h4 : (x - y) ^ 2 ≤ (4 / 3 : ℝ) := by
        linarith
      have h5 : (x - y) ≤ Real.sqrt (4 / 3 : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    have h4 : Real.sqrt (4 / 3 : ℝ) = (2 / Real.sqrt 3 : ℝ) := by
      have h11 : Real.sqrt (4 / 3 : ℝ) = (2 / Real.sqrt 3 : ℝ) := by
        have h1 : (4 / 3 : ℝ) = (2 / Real.sqrt 3) ^ 2 := by
          have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          field_simp [h2]
          nlinarith
        have h15 : Real.sqrt (4 / 3 : ℝ) = Real.sqrt ((2 / Real.sqrt 3) ^ 2) := by rw [h1]
        rw [h15]
        rw [Real.sqrt_sq (by
          have h2 : Real.sqrt 3 > 0 := by positivity
          positivity
        )]
      exact h11
    have h5 : (x - y) ≤ (2 / Real.sqrt 3 : ℝ) := by
      rw [h4] at h3'
      linarith
    have h6 : r = x - y := by linarith [hr]
    linarith