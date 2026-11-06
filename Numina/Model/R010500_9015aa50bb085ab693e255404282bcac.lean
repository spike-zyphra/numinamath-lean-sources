import Mathlib
theorem algebra_9062 (m:ℝ)(hf:∃ (a:ℝ),∀ (x:ℝ), (x^a) =  (m - 2) * x^(m^2 - 2 * m)) :m = 3 := by
  rcases hf with ⟨a,ha⟩
  have h1 := ha 1
  norm_num at h1

  linarith