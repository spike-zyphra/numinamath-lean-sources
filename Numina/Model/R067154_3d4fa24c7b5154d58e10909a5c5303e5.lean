import Mathlib

theorem algebra_152135 {f : ℝ → ℝ} (h : ∀ x y, f x + f (2 * x + y) + 5 * x * y = f (3 * x - y) + 2 * x ^ 2 + 1) :
    f 10 = -49 := by
  have eq1 : ∀ x, f x + f (2 * x) = f (3 * x) + 2 * x ^ 2 + 1 := by
    intro x
    specialize h x 0
    norm_num at h
    linarith
  have eq2 : ∀ x, f x + f (3 * x) = f (2 * x) - 3 * x ^ 2 + 1 := by
    intro x
    specialize h x x
    have eq3 : 2 * x + x = 3 * x := by ring
    have eq4 : 3 * x - x = 2 * x := by ring
    rw [eq3, eq4] at h
    have eq5 : 5 * x * x = 5 * x ^ 2 := by ring
    rw [eq5] at h
    linarith
  have eq3 : ∀ x, f x = - (x ^ 2) / 2 + 1 := by
    intro x
    have eq1_x := eq1 x
    have eq2_x := eq2 x
    linarith
  have h10 : f 10 = - (10 ^ 2) / 2 + 1 := eq3 10
  rw [h10]
  norm_num