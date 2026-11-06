import Mathlib

theorem algebra_2939 {a b c d : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 3 + b * x ^ 2 + c * x + d) (h2 : f 2 = 1) (h3 : f 3 = 4) (h4 : f 4 = 9) (h5 : f 5 = 34) : a + b + c + d = -18 := by
  simp [hf] at h2 h3 h4 h5
  linarith