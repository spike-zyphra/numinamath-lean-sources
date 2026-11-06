import Mathlib

theorem algebra_188231 {x y z : ℝ} (h : x = 2 * y ^ 2 / (1 + z ^ 2)) (h' : y = 2 * z ^ 2 / (1 + x ^ 2))
    (h'' : z = 2 * x ^ 2 / (1 + y ^ 2)) :
    (x, y, z) = (0, 0, 0) ∨ (x, y, z) = (1, 1, 1) := by

  have h1 : 1 + z ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg z]

  have h2 : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]

  have h3 : 1 + y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg y]

  have eq1 : x * (1 + z ^ 2) = 2 * y ^ 2 := by
    have h4 : 1 + z ^ 2 ≠ 0 := h1
    field_simp at h ⊢ 
    nlinarith

  have eq2 : y * (1 + x ^ 2) = 2 * z ^ 2 := by
    have h5 : 1 + x ^ 2 ≠ 0 := h2
    field_simp at h' ⊢
    nlinarith

  have eq3 : z * (1 + y ^ 2) = 2 * x ^ 2 := by
    have h6 : 1 + y ^ 2 ≠ 0 := h3
    field_simp at h'' ⊢
    nlinarith

  have eq4 : x = 0 ∨ x = 1 := by
    have h5 : x * (x - 1) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - 0),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_nonneg (sq_nonneg (x - 0)) (sq_nonneg (y - 0)), 
        mul_nonneg (sq_nonneg (y - 0)) (sq_nonneg (z - 0)), 
        mul_nonneg (sq_nonneg (z - 0)) (sq_nonneg (x - 0)), 
        mul_nonneg (sq_nonneg (x - 1)) (sq_nonneg (y - 1)), 
        mul_nonneg (sq_nonneg (y - 1)) (sq_nonneg (z - 1)), 
        mul_nonneg (sq_nonneg (z - 1)) (sq_nonneg (x - 1)), 
        sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x)
      ]
    cases (mul_eq_zero.1 h5) with 
    | inl h9 => 
      left
      linarith
    | inr h10 => 
      right
      nlinarith

  cases eq4 with
  | inl hx0 =>
    have hy0 : y = 0 := by
      nlinarith [hx0, eq1, eq2, eq3, sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - 0)]
    have hz0 : z = 0 := by
      nlinarith [hx0, eq1, eq2, eq3, sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - 0)]
    left
    simp [hx0, hy0, hz0]

  | inr hx1 =>
    have hy1 : y = 1 := by
      nlinarith [hx1, eq1, eq2, eq3, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hz1 : z = 1 := by
      nlinarith [hx1, eq1, eq2, eq3, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    right
    simp [hx1, hy1, hz1]