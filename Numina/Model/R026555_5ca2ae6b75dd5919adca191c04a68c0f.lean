import Mathlib

theorem algebra_242442 {x y z : ℝ}
    (h1 : x^2 = (y - z)^2 - 3) (h2 : y^2 = (z - x)^2 - 7) (h3 : z^2 = (x - y)^2 + 21) :
    (x = -1 ∧ y = -3 ∧ z = -5) ∨ (x = 1 ∧ y = 3 ∧ z = 5) := by
  have h4 : (x - 1) * (x + 1) = 0 := by
    nlinarith [sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y)]
  have hx1 : x = 1 ∨ x = -1 := by
    cases (mul_eq_zero.1 h4) with
    | inl h4a =>
      left
      linarith
    | inr h4b =>
      right
      linarith
  have h5 : (y - 3) * (y + 3) = 0 := by
    nlinarith [sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y)]
  have hy1 : y = 3 ∨ y = -3 := by
    cases (mul_eq_zero.1 h5) with
    | inl h5a =>
      left
      linarith
    | inr h5b =>
      right
      linarith
  have h6 : (z - 5) * (z + 5) = 0 := by
    nlinarith [sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y)]
  have hz1 : z = 5 ∨ z = -5 := by
    cases (mul_eq_zero.1 h6) with
    | inl h6a =>
      left
      linarith
    | inr h6b =>
      right
      linarith
  rcases hx1 with hx1 | hx1 <;> rcases hy1 with hy1 | hy1 <;> rcases hz1 with hz1 | hz1 <;> 
    norm_num [hx1, hy1, hz1] at h1 h2 h3 ⊢ <;> 
      try { tauto }