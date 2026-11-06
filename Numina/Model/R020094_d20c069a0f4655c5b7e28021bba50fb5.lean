import Mathlib

theorem algebra_195878 {x : ℝ} (hx : x ≠ 0) (h : x ^ 4 + x ^ 2 = y) :
    ¬∃! x, y = x ^ 4 + x ^ 2 := by

  rintro ⟨x', ⟨hx1, hx2⟩⟩

  have h1 : y = x' ^ 4 + x' ^ 2 := hx1
  -- Now, if we let z = -x', then y = (-x')^4 + (-x')^2, so by uniqueness of the solution, we get -x' = x'
  have h3 : -x' = x' := by
    have hx4 : y = (-x') ^ 4 + (-x') ^ 2 := by 
      nlinarith [h1]
    specialize hx2 (-x') hx4
    linarith

  have h4 : x' = (0 : ℝ) := by
    linarith

  have h5 : y = (0 : ℝ) := by 
    rw [h4] at h1
    nlinarith

  -- from h: x ^ 4 + x ^ 2 = y. Hence x^4 + x^2 = 0. Hence x^4 = -x^2, which is impossible for non-zero x
  have h6 : x ^ 4 + x ^ 2 = 0 := by
    linarith [h, h5]

  have h7 : x^2 * (x^2 + 1) = 0 := by
    nlinarith [h6]

  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- x^2 = 0
    have h10 : x ^ 2 = 0 := by
      linarith
    have h11 : x = 0 := by
      nlinarith
    contradiction
  · -- x^2 + 1 = 0
    have h12 : x ^ 2 = -1 := by 
      nlinarith
    nlinarith [sq_nonneg x]