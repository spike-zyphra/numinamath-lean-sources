import Mathlib

theorem algebra_282013 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    min (min (min (min x (x^2)) (2 * x)) (Real.sqrt x)) (1 / x) = x^2 := by
  rcases hx with ⟨hx1, hx2⟩
  -- Show x^2 < x
  have h1 : x ^ 2 < x := by
    nlinarith
  -- Show x^2 < 2x
  have h2 : x ^ 2 < 2 * x := by
    nlinarith
  -- Show that x < sqrt(x)
  have h3 : x < Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), sq_nonneg (Real.sqrt x - x)]
  -- Show x^2 < sqrt(x)
  have h4 : x ^ 2 < Real.sqrt x := by
    nlinarith [h1, h3]
  -- Show x^2 < 1/x
  have h5 : x ^ 2 < 1 / x := by
    have hx3 : 0 < (x : ℝ) := hx1
    have hx4 : x < 1 := hx2
    have hx7 : x ^ 3 - 1 < 0 := by
      have hx6 : x < (1 : ℝ) := hx2
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1), mul_pos hx1 (show 0 < x by linarith)]
    have hx8 : x ^ 2 - (1 / x) < 0 := by
      have hx9 : x ^ 2 - (1 / x) = (x ^ 3 - 1) / x := by
        field_simp
        <;> ring
      rw [hx9]
      apply div_neg_of_neg_of_pos
      linarith
      linarith
    linarith
  -- Calculate the minimum step by step
  have h1' : min x (x^2) = x ^ 2 := by
    apply min_eq_right
    linarith [h1]
  have h2' : min (min x (x^2)) (2 * x) = x ^ 2 := by
    rw [h1']
    apply min_eq_left
    linarith [h2]
  have h3' : min (min (min x (x^2)) (2 * x)) (Real.sqrt x) = x ^ 2 := by
    rw [h2']
    apply min_eq_left
    linarith [h4]
  rw [h3']
  apply min_eq_left
  linarith [h5]