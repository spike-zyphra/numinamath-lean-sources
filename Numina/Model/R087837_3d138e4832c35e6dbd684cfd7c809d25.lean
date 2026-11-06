import Mathlib

theorem algebra_235342 {x y z : ℝ} (hzz : y * z ≠ 0) (h1 : 2 * x = y) (h2 : 3 * z = 2 * x ^ 2) (h3 : x * y = 3 * x * z) :
    x = 1 := by
  have hy : y ≠ 0 := by
    by_contra h
    have h' : y * z = 0 := by
      rw [h]
      ring
    contradiction
  have hz : z ≠ 0 := by
    by_contra h
    have h' : y * z = 0 := by
      rw [h]
      ring
    contradiction
  have eq1 : y = 2 * x := by linarith
  have eq2 : z = (2 * x ^ 2) / 3 := by
    linarith
  rw [eq1] at h3
  rw [eq2] at h3
  have eq3 : 2 * x ^ 3 - 2 * x ^ 2 = 0 := by
    nlinarith
  have eq4 : 2 * x^2 * (x - 1) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp eq4) with
  | inl h4 =>
    have hx1 : x ^ 2 = 0 := by
      nlinarith
    have hx2 : x = 0 := by
      rw [sq_eq_zero_iff] at hx1
      exact hx1
    have hy1 : y = 0 := by
      rw [hx2] at eq1
      linarith
    contradiction
  | inr h5 =>
    have hx : x = 1 := by
      linarith
    exact hx