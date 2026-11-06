import Mathlib

open Real Set

theorem inequalities_111874 (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    (x y z : ℝ) (h : a^x + a^y + a^z + a^(-x) + a^(-y) + a^(-z) = 10) :
    1 ≤ a^x + a^y + a^z ∧ a^x + a^y + a^z ≤ 9 := by
  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  have h1 : a^x > 0 := by positivity
  have h2 : a^y > 0 := by positivity
  have h3 : a^z > 0 := by positivity
  have h4 : a^(-x) = 1 / a^x := by
    rw [show a^(-x) = (a^x)⁻¹ by rw [Real.rpow_neg]; all_goals linarith]
    field_simp
  have h5 : a^(-y) = 1 / a^y := by
    rw [show a^(-y) = (a^y)⁻¹ by rw [Real.rpow_neg]; all_goals linarith]
    field_simp
  have h6 : a^(-z) = 1 / a^z := by
    rw [show a^(-z) = (a^z)⁻¹ by rw [Real.rpow_neg]; all_goals linarith]
    field_simp
  have h7 : a^x + a^y + a^z + 1 / a^x + 1 / a^y + 1 / a^z = 10 := by
    rw [h4] at h
    rw [h5] at h
    rw [h6] at h
    linarith
  have h8 : a^x + a^y + a^z > 0 := by positivity
  have h9 : a^x + a^y + a^z ≤ 9 := by
    have h10 : (1 / a^x + 1 / a^y + 1 / a^z) ≥ 9 / (a^x + a^y + a^z) := by
      have h11 : a^x + a^y + a^z > 0 := by positivity
      have h14 : (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) ≥ 9 := by
        have h15 : (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) = 3 + (a^x / a^y + a^y / a^x) + (a^x / a^z + a^z / a^x) + (a^y / a^z + a^z / a^y) := by
          field_simp
          ring
        rw [h15]
        have h18 : a^x / a^y + a^y / a^x ≥ 2 := by
          have h19 : a^x / a^y + a^y / a^x - 2 ≥ 0 := by
            have h20 : a^x / a^y + a^y / a^x - 2 = ( (a^x)^2 + (a^y)^2 - 2 * a^x * a^y ) / (a^x * a^y) := by
              field_simp
              ring
            rw [h20]
            have h21 : (a^x)^2 + (a^y)^2 - 2 * a^x * a^y ≥ 0 := by
              have h22 : (a^x - a^y) ^ 2 ≥ 0 := sq_nonneg (a^x - a^y)
              linarith
            have h23 : a^x * a^y > 0 := mul_pos h1 h2
            apply div_nonneg h21 (by positivity)
          linarith
        have h19 : a^x / a^z + a^z / a^x ≥ 2 := by
          have h20 : a^x / a^z + a^z / a^x - 2 ≥ 0 := by
            have h21 : a^x / a^z + a^z / a^x - 2 = ( (a^x)^2 + (a^z)^2 - 2 * a^x * a^z ) / (a^x * a^z) := by
              field_simp
              ring
            rw [h21]
            have h22 : (a^x)^2 + (a^z)^2 - 2 * a^x * a^z ≥ 0 := by
              have h23 : (a^x - a^z) ^ 2 ≥ 0 := sq_nonneg (a^x - a^z)
              linarith
            have h24 : a^x * a^z > 0 := mul_pos h1 h3
            apply div_nonneg h22 (by positivity)
          linarith
        have h20 : a^y / a^z + a^z / a^y ≥ 2 := by
          have h21 : a^y / a^z + a^z / a^y - 2 ≥ 0 := by
            have h22 : a^y / a^z + a^z / a^y - 2 = ( (a^y)^2 + (a^z)^2 - 2 * a^y * a^z ) / (a^y * a^z) := by
              field_simp
              ring
            rw [h22]
            have h23 : (a^y)^2 + (a^z)^2 - 2 * a^y * a^z ≥ 0 := by
              have h24 : (a^y - a^z) ^ 2 ≥ 0 := sq_nonneg (a^y - a^z)
              linarith
            have h25 : a^y * a^z > 0 := mul_pos h2 h3
            apply div_nonneg h23 (by positivity)
          linarith
        linarith
      have h15 : (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) - 9 ≥ 0 := by linarith
      have h17 : (a^x + a^y + a^z) > 0 := by positivity
      have h18 : (1 / a^x + 1 / a^y + 1 / a^z) - 9 / (a^x + a^y + a^z) ≥ 0 := by
        have h19 : (1 / a^x + 1 / a^y + 1 / a^z) - 9 / (a^x + a^y + a^z) = ( (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) - 9 ) / (a^x + a^y + a^z) := by
          field_simp
          <;> ring
        rw [h19]
        apply div_nonneg h15 (by positivity)
      linarith
    have h25 : (a^x + a^y + a^z) + (1 / a^x + 1 / a^y + 1 / a^z) = 10 := by linarith
    have h27 : (a^x + a^y + a^z) + 9 / (a^x + a^y + a^z) ≤ 10 := by
      have h30 : (1 / a^x + 1 / a^y + 1 / a^z) ≥ 9 / (a^x + a^y + a^z) := h10
      have h31 : (a^x + a^y + a^z) + (1 / a^x + 1 / a^y + 1 / a^z) = 10 := by linarith
      nlinarith
    have h37 : (a^x + a^y + a^z)^2 + 9 ≤ 10 * (a^x + a^y + a^z) := by
      have h38 : (a^x + a^y + a^z) > 0 := by positivity
      have h39 : (a^x + a^y + a^z) + 9 / (a^x + a^y + a^z) ≤ 10 := h27
      have h40 : (a^x + a^y + a^z) * ((a^x + a^y + a^z) + 9 / (a^x + a^y + a^z)) ≤ (a^x + a^y + a^z) * 10 := by
        apply mul_le_mul_of_nonneg_left h27 (by positivity)
      have h41 : (a^x + a^y + a^z) * ((a^x + a^y + a^z) + 9 / (a^x + a^y + a^z)) = (a^x + a^y + a^z)^2 + 9 := by
        field_simp
        <;> nlinarith
      nlinarith [h41, h40]
    have h37 : (a^x + a^y + a^z)^2 - 10 * (a^x + a^y + a^z) + 9 ≤ 0 := by
      nlinarith
    have h38 : (a^x + a^y + a^z - 1) * (a^x + a^y + a^z - 9) ≤ 0 := by
      nlinarith
    have h39 : a^x + a^y + a^z ≤ 9 := by
      nlinarith [show a^x + a^y + a^z > 0 by positivity]
    linarith
  have h100 : 1 ≤ a^x + a^y + a^z := by
    have h10 : (1 / a^x + 1 / a^y + 1 / a^z) ≥ 9 / (a^x + a^y + a^z) := by
      have h11 : a^x + a^y + a^z > 0 := by positivity
      have h14 : (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) ≥ 9 := by
        have h15 : (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) = 3 + (a^x / a^y + a^y / a^x) + (a^x / a^z + a^z / a^x) + (a^y / a^z + a^z / a^y) := by
          field_simp
          ring
        rw [h15]
        have h18 : a^x / a^y + a^y / a^x ≥ 2 := by
          have h19 : a^x / a^y + a^y / a^x - 2 ≥ 0 := by
            have h20 : a^x / a^y + a^y / a^x - 2 = ( (a^x)^2 + (a^y)^2 - 2 * a^x * a^y ) / (a^x * a^y) := by
              field_simp
              ring
            rw [h20]
            have h21 : (a^x)^2 + (a^y)^2 - 2 * a^x * a^y ≥ 0 := by
              have h22 : (a^x - a^y) ^ 2 ≥ 0 := sq_nonneg (a^x - a^y)
              linarith
            have h23 : a^x * a^y > 0 := mul_pos h1 h2
            apply div_nonneg h21 (by positivity)
          linarith
        have h19 : a^x / a^z + a^z / a^x ≥ 2 := by
          have h20 : a^x / a^z + a^z / a^x - 2 ≥ 0 := by
            have h21 : a^x / a^z + a^z / a^x - 2 = ( (a^x)^2 + (a^z)^2 - 2 * a^x * a^z ) / (a^x * a^z) := by
              field_simp
              ring
            rw [h21]
            have h22 : (a^x)^2 + (a^z)^2 - 2 * a^x * a^z ≥ 0 := by
              have h23 : (a^x - a^z) ^ 2 ≥ 0 := sq_nonneg (a^x - a^z)
              linarith
            have h24 : a^x * a^z > 0 := mul_pos h1 h3
            apply div_nonneg h22 (by positivity)
          linarith
        have h20 : a^y / a^z + a^z / a^y ≥ 2 := by
          have h21 : a^y / a^z + a^z / a^y - 2 ≥ 0 := by
            have h22 : a^y / a^z + a^z / a^y - 2 = ( (a^y)^2 + (a^z)^2 - 2 * a^y * a^z ) / (a^y * a^z) := by
              field_simp
              ring
            rw [h22]
            have h23 : (a^y)^2 + (a^z)^2 - 2 * a^y * a^z ≥ 0 := by
              have h24 : (a^y - a^z) ^ 2 ≥ 0 := sq_nonneg (a^y - a^z)
              linarith
            have h25 : a^y * a^z > 0 := mul_pos h2 h3
            apply div_nonneg h23 (by positivity)
          linarith
        linarith
      have h15 : (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) - 9 ≥ 0 := by linarith
      have h17 : (a^x + a^y + a^z) > 0 := by positivity
      have h18 : (1 / a^x + 1 / a^y + 1 / a^z) - 9 / (a^x + a^y + a^z) ≥ 0 := by
        have h19 : (1 / a^x + 1 / a^y + 1 / a^z) - 9 / (a^x + a^y + a^z) = ( (a^x + a^y + a^z) * (1 / a^x + 1 / a^y + 1 / a^z) - 9 ) / (a^x + a^y + a^z) := by
          field_simp
          <;> ring
        rw [h19]
        apply div_nonneg h15 (by positivity)
      linarith
    have h25 : (a^x + a^y + a^z) + (1 / a^x + 1 / a^y + 1 / a^z) = 10 := by linarith
    have h27 : (a^x + a^y + a^z) + 9 / (a^x + a^y + a^z) ≤ 10 := by
      have h30 : (1 / a^x + 1 / a^y + 1 / a^z) ≥ 9 / (a^x + a^y + a^z) := h10
      have h31 : (a^x + a^y + a^z) + (1 / a^x + 1 / a^y + 1 / a^z) = 10 := by linarith
      nlinarith
    have h37 : (a^x + a^y + a^z)^2 + 9 ≤ 10 * (a^x + a^y + a^z) := by
      have h38 : (a^x + a^y + a^z) > 0 := by positivity
      have h39 : (a^x + a^y + a^z) + 9 / (a^x + a^y + a^z) ≤ 10 := h27
      have h40 : (a^x + a^y + a^z) * ((a^x + a^y + a^z) + 9 / (a^x + a^y + a^z)) ≤ (a^x + a^y + a^z) * 10 := by
        apply mul_le_mul_of_nonneg_left h27 (by positivity)
      have h41 : (a^x + a^y + a^z) * ((a^x + a^y + a^z) + 9 / (a^x + a^y + a^z)) = (a^x + a^y + a^z)^2 + 9 := by
        field_simp
        <;> nlinarith
      nlinarith [h41, h40]
    have h37 : (a^x + a^y + a^z)^2 - 10 * (a^x + a^y + a^z) + 9 ≤ 0 := by
      nlinarith
    have h38 : (a^x + a^y + a^z - 1) * (a^x + a^y + a^z - 9) ≤ 0 := by
      nlinarith
    have h39 : a^x + a^y + a^z ≥ 1 := by
      nlinarith [show a^x + a^y + a^z > 0 by positivity]
    linarith
  constructor
  · linarith
  · linarith