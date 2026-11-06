import Mathlib

theorem algebra_257398 {f : ℝ → ℝ} (hf : ∀ x, f (9 * x) / f (3 * x) = (243 * x - 729) / (x - 81)) :
    f = fun x => (x - 27) ^ 2 * (x - 81) * (x - 243) := by

  have h1 := hf 0
  norm_num at h1
  all_goals by_cases h : f 0 = 0 <;> simp [h] at h1 <;> linarith