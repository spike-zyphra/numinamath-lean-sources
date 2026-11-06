import Mathlib

theorem algebra_315627 {f : ℝ → ℝ}
    (h : ∀ x y, f x + f (2 * x + y) + 5 * x * y = f (3 * x - y) + 2 * x ^ 2 + 1) :
    f 10 = -49 := by
  have h1 : ∀ x, f x = -1/2 * x ^ 2 + 1 := by
    intro x
    have eq1 := h x (x / 2)
    have eq2 : 2 * x + (x / 2) = 5 * x / 2 := by ring
    have eq3 : 3 * x - (x / 2) = 5 * x / 2 := by ring
    rw [eq2, eq3] at eq1
    have eq4 : f x + f (5 * x / 2) + (5 * x * (x / 2)) = f (5 * x / 2) + 2 * x^2 + 1 := by
      linarith [eq1]
    have eq5 : f x = -1/2 * x ^ 2 + 1 := by
      nlinarith [eq4]
      <;> ring_nf
      <;> nlinarith
    exact eq5
  have h10 := h1 10
  norm_num at h10
  linarith [h10]