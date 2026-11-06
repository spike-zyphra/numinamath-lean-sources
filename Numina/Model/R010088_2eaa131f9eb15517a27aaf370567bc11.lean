import Mathlib

theorem algebra_15182 {p : ℝ → ℝ} (hp : ∃ a b c d, p = fun x => a*x^3 + b*x^2 + c*x + d)
    (h1 : p 1 = 1 / 1 ^ 2) (h2 : p 2 = 1 / 2 ^ 2) (h3 : p 3 = 1 / 3 ^ 2)
    (h4 : p 4 = 1 / 4 ^ 2) : p 5 = -5 / 12 := by
  rcases hp with ⟨a, b, c, d, hp⟩
  have eq1 : p 1 = a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d := by
    rw [hp]
  have eq2 : p 2 = a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d := by
    rw [hp]
  have eq3 : p 3 = a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d := by
    rw [hp]
  have eq4 : p 4 = a * 4 ^ 3 + b * 4 ^ 2 + c * 4 + d := by
    rw [hp]
  have eq5 : p 5 = a * 5 ^ 3 + b * 5 ^ 2 + c * 5 + d := by
    rw [hp]
  rw [eq1] at h1
  rw [eq2] at h2
  rw [eq3] at h3
  rw [eq4] at h4
  rw [eq5] at *
  norm_num at h1 h2 h3 h4 ⊢
  linarith