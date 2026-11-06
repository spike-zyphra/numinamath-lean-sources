import Mathlib

theorem algebra_189097 (f : ℝ → ℝ) (c : ℝ) (hf : f = fun x => Real.arctan ((2 - 2 * x) / (1 + 4 * x)) + c)
    (hodd : ∀ x ∈ Set.Ioo (-1 / 4) (1 / 4), f (-x) = -f x) :
    c = -Real.arctan 2 := by
  have h0 := hodd 0 (by norm_num)
  simp [hf] at h0
  norm_num at h0 
  linarith