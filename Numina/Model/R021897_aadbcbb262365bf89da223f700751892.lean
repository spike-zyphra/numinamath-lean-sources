import Mathlib

theorem algebra_297493 {x y z : ℝ} (h1 : 4 * x ^ 2 / (1 + 4 * x ^ 2) = y) (h2 : 4 * y ^ 2 / (1 + 4 * y ^ 2) = z)
    (h3 : 4 * z ^ 2 / (1 + 4 * z ^ 2) = x) :
    x = 0 ∧ y = 0 ∧ z = 0 ∨ x = 1 / 2 ∧ y = 1 / 2 ∧ z = 1 / 2 := by

  -- Prove x ≥ 0
  have hy1 : y ≥ 0 := by
    have h1' : 4 * x ^ 2 / (1 + 4 * x ^ 2) = y := h1
    have pos1 : 1 + 4 * x ^ 2 > 0 := by
      nlinarith [sq_nonneg x]
    have h4 : 4 * x ^ 2 ≥ 0 := by nlinarith [sq_nonneg x]
    have h5 : (4 * x ^ 2) / (1 + 4 * x ^ 2) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals linarith
    linarith [h1']

  -- Prove z ≥ 0
  have hz1 : z ≥ 0 := by
    have h2' : 4 * y ^ 2 / (1 + 4 * y ^ 2) = z := h2
    have pos2 : 1 + 4 * y ^ 2 > 0 := by
      nlinarith [sq_nonneg y]
    have h4 : 4 * y ^ 2 ≥ 0 := by nlinarith [sq_nonneg y]
    have h5 : (4 * y ^ 2) / (1 + 4 * y ^ 2) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals linarith
    linarith [h2']

  -- Prove x ≥ 0
  have hx1 : x ≥ 0 := by
    have h3' : 4 * z ^ 2 / (1 + 4 * z ^ 2) = x := h3
    have pos3 : 1 + 4 * z ^ 2 > 0 := by
      nlinarith [sq_nonneg z]
    have h4 : 4 * z ^ 2 ≥ 0 := by nlinarith [sq_nonneg z]
    have h5 : (4 * z ^ 2) / (1 + 4 * z ^ 2) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals linarith
    linarith [h3']

  have h5 : x = 0 ∨ x = 1 / 2 := by
    have eq1 : x ≥ 0 := hx1

    have h6 : x^2 ≤ x := by
      field_simp at h1 h2 h3
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2), h1, h2, h3]

    have h7 : x ≤ 1 := by nlinarith [sq_nonneg (x - 1 / 2), hx1, h6]

    -- Take product of the three equations and simplify to get the cubic equation
    have h8 : x * (2 * x - 1) ^ 2 = 0 := by
      field_simp at h1 h2 h3
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2), h1, h2, h3]

    cases' (mul_eq_zero.mp h8) with hx2 hx3
    · -- Case where x = 0
      left
      linarith
    · -- Case where (2x - 1)^2 = 0
      right
      nlinarith

  cases' h5 with hx0 hx1
  · -- When x = 0
    have hx0 : x = 0 := hx0
    have hy0 : y = 0 := by
      rw [hx0] at h1
      norm_num at h1 ⊢
      linarith
    have hz0 : z = 0 := by
      rw [hy0] at h2
      norm_num at h2 ⊢
      linarith
    left
    exact ⟨hx0, hy0, hz0⟩
  · -- When x = 1/2
    have hx1_2_eq_x : x = 1 / 2 := hx1
    have hy1_2_eq : y = 1 / 2 := by
      rw [hx1_2_eq_x] at h1
      norm_num at h1 ⊢
      nlinarith
    have hz1_2_eq : z = 1 / 2 := by
      rw [hy1_2_eq] at h2
      norm_num at h2 ⊢
      nlinarith
    right
    exact ⟨hx1_2_eq_x, hy1_2_eq, hz1_2_eq⟩