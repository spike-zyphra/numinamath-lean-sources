import Mathlib

  theorem algebra_19365 {x y : ℝ} (hx : x^2-4*x-14=3*x+16) (hy : y^2-4*y-14=3*y+16)
  (hxy : x≠y) : |x-y| = 13 := by
    have h1 : x^2 - 7 * x - 30 = 0 := by linarith
    have h2 : y^2 - 7 * y - 30 = 0 := by linarith
    have h3 : (x - 10) * (x + 3) = 0 := by
      linarith [h1]
    have h4 : (y - 10) * (y + 3) = 0 := by
      linarith [h2]
    have h5 : x = 10 ∨ x = -3 := by
      cases (mul_eq_zero.mp h3) with
      | inl h6 =>
        left
        linarith
      | inr h7 =>
        right
        linarith
    have h6 : y = 10 ∨ y = -3 := by
      cases (mul_eq_zero.mp h4) with
      | inl h7 =>
        left
        linarith
      | inr h8 =>
        right
        linarith
    cases h5 with
    | inl hx10 =>
      cases h6 with
      | inl hy10 =>
        exfalso
        exact hxy (by linarith)
      | inr hy3 =>
        rw [hx10, hy3]
        norm_num [abs_of_nonneg]
    | inr hx3 =>
      cases h6 with
      | inl hy10 =>
        rw [hx3, hy10]
        norm_num [abs_of_nonneg]
      | inr hy3 =>
        exfalso
        exact hxy (by linarith)