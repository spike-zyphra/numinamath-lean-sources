import Mathlib

  theorem algebra_19365 {x y : ℝ} (hx : x^2-4*x-14=3*x+16) (hy : y^2-4*y-14=3*y+16)
  (hxy : x≠y) : |x-y| = 13 := by
    have eq1 : x^2 - 7 * x - 30 = 0 := by linarith
    have eq2 : y^2 - 7 * y - 30 = 0 := by linarith
    have h1 : (x - 10) * (x + 3) = 0 := by
      linarith [eq1]
    have h2 : (y - 10) * (y + 3) = 0 := by
      linarith [eq2]
    have hx_eq_10_or_neg3 : x = 10 ∨ x = -3 := by 
      cases (mul_eq_zero.mp h1) with
      | inl h1l => left; linarith
      | inr h1r => right; linarith
    have hy_eq_10_or_neg3 : y = 10 ∨ y = -3 := by 
      cases (mul_eq_zero.mp h2) with
      | inl h2l => left; linarith
      | inr h2r => right; linarith
    cases hx_eq_10_or_neg3 with
    | inl hx10 =>
      cases hy_eq_10_or_neg3 with
      | inl hy10 =>
        exfalso
        exact hxy (by linarith)
      | inr hy_neg3 =>
        have : x - y = 13 := by
          rw [hx10, hy_neg3]
          linarith
        rw [abs_of_pos (by linarith)]
        linarith
    | inr hx_neg3 =>
      cases hy_eq_10_or_neg3 with
      | inl hy10 =>
        have : x - y = -13 := by
          rw [hx_neg3, hy10]
          linarith
        rw [abs_of_neg (by linarith)]
        linarith
      | inr hy_neg3 =>
        exfalso
        exact hxy (by linarith)