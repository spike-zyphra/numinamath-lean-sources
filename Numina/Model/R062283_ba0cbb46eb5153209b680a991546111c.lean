import Mathlib

theorem algebra_320304 {a b c d : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (h1 : f 1 = 1) (h2 : f 2 = 2) (h3 : f 3 = 3) :
    (1 / 4) * (f 4 + f 0) = 7 := by
  have eq1 : 1 ^ 4 + a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d = 1 := by
    rw [hf 1] at h1
    exact h1
  have eq2 : 2 ^ 4 + a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 2 := by
    rw [hf 2] at h2
    exact h2
  have eq3 : 3 ^ 4 + a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 3 := by
    rw [hf 3] at h3
    exact h3
  have eq4 : f 4 = 4 ^ 4 + a * 4 ^ 3 + b * 4 ^ 2 + c * 4 + d := by
    apply hf
  have eq5 : f 0 = 0 ^ 4 + a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d := by
    apply hf
  rw [eq4, eq5]
  ring_nf at eq1 eq2 eq3 ⊢
  linarith