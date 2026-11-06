import Mathlib

theorem algebra_94420 {p : ℝ} (hp : 0 < p) (x : ℝ) (hx : x * (1 + p / 100) * (1 - p / 100) = 1) :
    x = 10000 / (10000 - p ^ 2) := by
  have eq1 : x * (1 + p / 100) * (1 - p / 100) = x * (1 - (p / 100) ^ 2) := by
    ring
  rw [eq1] at hx
  have eq2 : x * (1 - (p / 100) ^ 2) = x * (1 - p^2 / 10000) := by
    ring_nf
  rw [eq2] at hx
  have eq4 : x * (10000 - p^2) = 10000 := by
    field_simp at hx ⊢
    nlinarith
  have eq5 : 10000 - p^2 ≠ 0 := by
    by_contra h
    have eq5 : p^2 = 10000 := by linarith
    have eq6 : p = 100 := by nlinarith [eq5, show p > 0 by linarith]
    rw [eq6] at hx
    nlinarith
  have eq6 : x = 10000 / (10000 - p^2) := by
    field_simp [eq5]
    linarith
  exact eq6