import Mathlib


theorem algebra_145597 {x y : ℝ} (h1 : x^2 * y - x * y^2 - 3 * x + 3 * y + 1 = 0) (h2 : x^3 * y - x * y^3 - 3 * x^2 + 3 * y^2 + 3 = 0) :
    x = 2 ∧ y = 1 := by

  have eq1 : x + y = 3 := by
    have eq2 : (x^2 - y^2) * (x * y - 3) = -3 := by
      nlinarith [h2]
    have eq3 : (x - y) * (x * y - 3) = -1 := by
      nlinarith [h1]
    have h3 : (x + y) * ((x - y) * (x * y - 3)) = -3 := by
      nlinarith [eq2]
    rw [eq3] at h3
    nlinarith


  have eq2' : y = 3 - x := by linarith
  rw [eq2'] at h1

  have h3 : 2 * x ^ 3 - 9 * x ^ 2 + 15 * x - 10 = 0 := by
    nlinarith [h1]

  have h4 : (x - 2) * (2 * x ^ 2 - 5 * x + 5) = 0 := by
    nlinarith [h3]

  cases' (mul_eq_zero.mp h4) with h5 h6
  ·
    have hx : x = 2 := by linarith
    have hy : y = 1 := by
      rw [hx] at eq2'
      linarith
    exact ⟨hx, hy⟩
  ·
    have h7 : (2:ℝ) * x ^ 2 - 5 * x + 5 ≠ 0 := by
      intro h
      have h8 : (2:ℝ) * x ^ 2 - 5 * x + 5 = 0 := by linarith
      nlinarith [sq_nonneg (x - 5 / 4)]
    exfalso
    apply h7
    linarith