import Mathlib

theorem algebra_243270 {x y z : ℝ} (h1 : x + y - 2 + 4 * x * y = 0) (h2 : y + z - 2 + 4 * y * z = 0)
    (h3 : z + x - 2 + 4 * z * x = 0) :
    (x, y, z) = (-1, -1, -1) ∨ (x, y, z) = (1 / 2, 1 / 2, 1 / 2) := by
  have eq1 : (4 * x + 1) * (4 * y + 1) = 9 := by
    nlinarith
  have eq2 : (4 * y + 1) * (4 * z + 1) = 9 := by
    nlinarith
  have eq3 : (4 * z + 1) * (4 * x + 1) = 9 := by
    nlinarith
  have eq4 : (4 * x + 1) ^ 2 = 9 := by
    nlinarith [sq_nonneg (4 * x + 1), sq_nonneg (4 * y + 1), sq_nonneg (4 * z + 1),
      eq1, eq2, eq3
    ]
  have eq5 : (4 * y + 1) ^ 2 = 9 := by
    nlinarith [sq_nonneg (4 * x + 1), sq_nonneg (4 * y + 1), sq_nonneg (4 * z + 1),
      eq1, eq2, eq3
    ]
  have eq6 : (4 * z + 1) ^ 2 = 9 := by
    nlinarith [sq_nonneg (4 * x + 1), sq_nonneg (4 * y + 1), sq_nonneg (4 * z + 1),
      eq1, eq2, eq3
    ]
  have h4 : 4 * x + 1 = 3 ∨ 4 * x + 1 = -3 := by
    have h1 : (4 * x + 1) ^ 2 = 9 := eq4
    have h2 : 4 * x + 1 = 3 ∨ 4 * x + 1 = -3 := by
      have h3 : (4 * x + 1) ^ 2 - 9 = 0 := by linarith
      have h4 : (4 * x + 1 - 3) * (4 * x + 1 + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h4) with h5 h6
      · left
        linarith
      · right
        linarith
    exact h2
  cases h4 with
  | inl hx1 =>
    -- We know 4x+1 = 3, so find y and z
    have hx1' : 4 * x + 1 = 3 := hx1
    have hy1 : 4 * y + 1 = 3 := by
      nlinarith [eq1, hx1']
    have hz1 : 4 * z + 1 = 3 := by
      nlinarith [eq2, hy1]
    have hx2 : x = 1 / 2 := by
      linarith
    have hy2 : y = 1 / 2 := by
      linarith
    have hz2 : z = 1 / 2 := by
      linarith
    right
    simp [hx2, hy2, hz2]
  | inr hx1 =>
    -- We know 4x+1 = -3, so find y and z
    have hx1' : 4 * x + 1 = -3 := hx1
    have hy1 : 4 * y + 1 = -3 := by
      nlinarith [eq1, hx1']
    have hz1 : 4 * z + 1 = -3 := by
      nlinarith [eq2, hy1]
    have hx2 : x = -1 := by
      linarith
    have hy2 : y = -1 := by
      linarith
    have hz2 : z = -1 := by
      linarith
    left
    simp [hx2, hy2, hz2]