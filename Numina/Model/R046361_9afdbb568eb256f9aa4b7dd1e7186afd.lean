import Mathlib

open Real

theorem algebra_215271 :
    IsLeast {u : ℝ | ∃ x y : ℝ, x ∈ Set.Ioo (-2) 2 ∧ y ∈ Set.Ioo (-2) 2 ∧ x * y = -1 ∧ u = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)} (12 / 5) := by
  constructor
  · -- Show that 12/5 is in the set
    use Real.sqrt (2 / 3), -Real.sqrt (3 / 2)
    constructor
    · -- Show x ∈ (-2, 2)
      constructor
      · -- Show -2 < Real.sqrt (2 / 3)
        have h1 : 0 < Real.sqrt (2 / 3) := by positivity
        nlinarith [Real.sqrt_nonneg (2 / 3), Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by norm_num)]
      · -- Show Real.sqrt (2 / 3) < 2
        have h2 : Real.sqrt (2 / 3) < 2 := by
          nlinarith [Real.sqrt_nonneg (2 / 3), Real.sq_sqrt (show 0 ≤ (2 / 3 : ℝ) by norm_num)]
        linarith
    constructor
    · -- Show y ∈ (-2, 2)
      constructor
      · -- Show -2 < -Real.sqrt (3 / 2)
        have h3 : Real.sqrt (3 / 2) < 2 := by
          nlinarith [Real.sqrt_nonneg (3 / 2), Real.sq_sqrt (show 0 ≤ (3 / 2 : ℝ) by norm_num)]
        linarith
      · -- Show -Real.sqrt (3 / 2) < 2
        have h4 : -Real.sqrt (3 / 2) < 2 := by
          have h3 : 0 < Real.sqrt (3 / 2) := by positivity
          nlinarith [Real.sqrt_nonneg (3 / 2), Real.sq_sqrt (show 0 ≤ (3 / 2 : ℝ) by norm_num)]
        linarith
    constructor
    · -- Show x * y = -1
      have h2 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = 1 := by
        calc
          Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = Real.sqrt ((2 / 3) * (3 / 2)) := by
            rw [← Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 1 := by norm_num
          _ = (1 : ℝ) := by simp
      nlinarith [h2]
    · -- Show u = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)
      have hx2 : 4 - (Real.sqrt (2 / 3) : ℝ) ^ 2 = 10 / 3 := by
        have h12 : (Real.sqrt (2 / 3) : ℝ) ^ 2 = (2 / 3 : ℝ) := Real.sq_sqrt (by norm_num)
        linarith
      have hy2 : 9 - (-Real.sqrt (3 / 2) : ℝ) ^ 2 = 15 / 2 := by
        have h7 : (-Real.sqrt (3 / 2) : ℝ) ^ 2 = (3 / 2 : ℝ) := by
          have h23 : (Real.sqrt (3 / 2) : ℝ) ^ 2 = (3 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
          nlinarith
        nlinarith
      rw [hx2, hy2]
      norm_num
  · -- Show that 12/5 is the minimum
    intro u hu
    rcases hu with ⟨x, y, hx, hy, hxy, heq⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with  ⟨hy1, hy2⟩
    have h1 : -2 < x := by linarith
    have h2 : x < 2 := by linarith
    have h3 : -2 < y := by linarith
    have h4 : y < 2 := by linarith
    have h6 : y ^ 2 = 1 / x ^ 2 := by
      have h20 : x * y = -1 := by linarith
      have h30 : y = -1 / x := by
        have hx0 : x ≠ 0 := by
          by_contra h
          have h0 : x = 0 := by linarith
          rw [h0] at h20
          nlinarith
        field_simp
        linarith
      rw [h30]
      have hx0 : x ≠ 0 := by
        by_contra h
        have h0 : x = 0 := by linarith
        rw [h0] at hxy
        nlinarith
      field_simp
      <;> nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by assumption)]
    have h7 : 9 - y ^ 2 = 9 - (1 / x ^ 2) := by
      rw [h6]
    have h8 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) ≥ 12 / 5 := by
      have hx20 : 4 - x ^ 2 > 0 := by
        nlinarith [sq_nonneg x]
      have h18 : 9 - y ^ 2 > 0 := by
        have h30 : y ^ 2 < 4 := by
          nlinarith [sq_nonneg y]
        nlinarith [sq_nonneg y]
      have h14 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 ≥ 0 := by
        have h14 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 =
            (4 * (9 - y^2) * 5 + 9 * (4 - x^2) * 5 - 12 * (4 - x^2) * (9 - y^2)) / (5 * (4 - x^2) * (9 - y^2)) := by
          field_simp [(show (4 - x ^ 2 : ℝ) ≠ 0 by
            nlinarith
          ), (show (9 - y ^ 2 : ℝ) ≠ 0 by
            nlinarith
          ), (show (5 : ℝ) ≠ 0 by norm_num)]
          ring
        rw [h14]
        have h15 : (4 * (9 - y^2) * 5 + 9 * (4 - x^2) * 5 - 12 * (4 - x^2) * (9 - y^2)) ≥ 0 := by
          have h21 : y ^ 2 = 1 / x ^ 2 := h6
          rw [h21]
          have hx0 : x ≠ 0 := by
            by_contra h
            have h0 : x = 0 := by linarith
            rw [h0] at hxy
            nlinarith
          have h10 : x ^ 2 > 0 := by
            positivity
          have h11 : (4 * (9 - (1 / x ^ 2)) * 5 + 9 * (4 - x ^ 2) * 5 - 12 * (4 - x ^ 2) * (9 - (1 / x ^ 2)) ) =
              -84 + 63 * x^2 + 28 / x^2 := by
            field_simp
            ring
          rw [h11]
          have h17 : -84 + 63 * x^2 + 28 / x^2 ≥ 0 := by
            have h18 : x ^ 2 > 0 := by positivity
            have h17' : ( -84 + 63 * x^2 + 28 / x^2 ) = (63 * x ^ 4 - 84 * x ^ 2 + 28) / x ^ 2 := by
              field_simp
              ring
            rw [h17']
            have h19' : (63 * x ^ 4 - 84 * x ^ 2 + 28) = 7 * (3 * x ^ 2 - 2) ^ 2 := by nlinarith
            have h10' : (63 * x ^ 4 - 84 * x ^ 2 + 28) ≥ 0 := by
              rw [h19']
              have h122 : (3 * x ^ 2 - 2) ^ 2 ≥ 0 := by positivity
              nlinarith
            have h13' : x ^ 2 > 0 := by positivity
            apply div_nonneg
            all_goals nlinarith
          linarith
        have h18 : (5 * (4 - x ^ 2) * (9 - y ^ 2)) > 0 := by
          positivity
        apply div_nonneg
        · linarith
        · positivity
      linarith
    have heq' : u = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) := by
      linarith [heq]
    linarith