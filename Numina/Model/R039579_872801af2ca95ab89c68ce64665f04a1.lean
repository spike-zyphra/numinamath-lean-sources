import Mathlib

theorem algebra_604680{x y z: ℝ}(xpos: 0 < x)
  (ypos: 0 < y)(zpos: 0 < z):
  (1/x+4/y+9/z=3 ∧ x+y+z≤12) ↔ (x=2 ∧ y=4 ∧ z=6) := by
  constructor
  · -- First direction: from the equations to the values
    rintro ⟨h_eq, h_ineq⟩
    have h1 : 0 < x * y * z := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : x + y + z = 12 := by
      have h3 : (1 / x + 4 / y + 9 / z) * (x + y + z) ≥ 36 := by
        have h9 : (1 / x + 4 / y + 9 / z) * (x + y + z) - 36 ≥ 0 := by
          have h16 : (1 / x + 4 / y + 9 / z) * (x + y + z) - 36 =
              ( (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) ) / (x * y * z) := by
            field_simp
            nlinarith
          rw [h16]
          have h17 : 0 < x * y * z := by
            apply mul_pos
            apply mul_pos
            all_goals linarith
          have h18 : (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) ≥ 0 := by
            nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (z - 3 * x), sq_nonneg (z - 3 * y / 2), mul_pos xpos ypos, mul_pos xpos zpos, mul_pos ypos zpos, sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
          have h19 : ( (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) ) / (x * y * z) ≥ 0 := by
            apply div_nonneg
            · linarith
            · positivity
          linarith
        linarith
      have h20 : (1 / x + 4 / y + 9 / z) * (x + y + z) = 36 := by
        nlinarith [h_eq, h_ineq]
      have h21 : x + y + z = 12 := by
        nlinarith [h_eq, h20]
      linarith
    have h3 : y = 2 * x := by
      have h4 : (y - 2 * x) ^ 2 = 0 := by
        have h16 : (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) = 0 := by
          have h17 : (1 / x + 4 / y + 9 / z) * (x + y + z) = 36 := by
            nlinarith [h_eq, h2]
          have h18 : (1 / x + 4 / y + 9 / z) * (x + y + z) - 36 = 0 := by linarith
          have h19 : (1 / x + 4 / y + 9 / z) * (x + y + z) - 36 =
              ( (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) ) / (x * y * z) := by
            field_simp
            nlinarith
          rw [h19] at h18
          have h20 : x * y * z > 0 := by
            apply mul_pos
            apply mul_pos
            all_goals linarith
          have h21 : (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) = 0 := by
            field_simp at h18 ⊢
            nlinarith
          linarith
        nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (z - 3 * x), sq_nonneg (z - 3 * y / 2), mul_pos xpos ypos, mul_pos xpos zpos, mul_pos ypos zpos, sq_nonneg (x - 2), sq_nonneg (y - 4), sq_nonneg (z - 6)]
      nlinarith
    have h4 : z = 3 * x := by
      have h16 : (z - 3 * x) ^ 2 = 0 := by
        have h16 : (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) = 0 := by
          have h17 : (1 / x + 4 / y + 9 / z) * (x + y + z) = 36 := by
            nlinarith [h_eq, h2]
          have h18 : (1 / x + 4 / y + 9 / z) * (x + y + z) - 36 = 0 := by linarith
          have h19 : (1 / x + 4 / y + 9 / z) * (x + y + z) - 36 =
              ( (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) ) / (x * y * z) := by
            field_simp
            nlinarith
          rw [h19] at h18
          have h20 : x * y * z > 0 := by
            apply mul_pos
            apply mul_pos
            all_goals linarith
          have h21 : (y * z + 4 * x * z + 9 * x * y) * (x + y + z) - 36 * (x * y * z) = 0 := by
            field_simp at h18 ⊢
            nlinarith
          linarith
        nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (z - 3 * x), sq_nonneg (z - 3 * y / 2), mul_pos xpos ypos, mul_pos xpos zpos, mul_pos ypos zpos, sq_nonneg (x - 2), sq_nonneg (y - 4), sq_nonneg (z - 6)]
      nlinarith
    have hx2 : x = 2 := by
      nlinarith [h2, h3, h4]
    have hy2 : y = 4 := by
      nlinarith [h3, hx2]
    have hz2 : z = 6 := by
      nlinarith [h4, hx2]
    exact ⟨hx2, hy2, hz2⟩
  · -- Second direction: from the values to the system of equations.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Check the equation.
      norm_num
    · -- Check the inequality.
      norm_num