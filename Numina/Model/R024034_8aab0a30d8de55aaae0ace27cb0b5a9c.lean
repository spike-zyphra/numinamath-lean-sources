import Mathlib

open Real

theorem algebra_70413 {f : ℚ → ℝ} (hf : ∀ x, x ≠ 0 ∧ x ≠ 1 → f x + f (1 - 1 / x) = log (abs x)) :
    f 2007 = log (2007 / 2006) := by 
  have h1 := hf 2007 ⟨by norm_num, by norm_num⟩
  have h2 := hf (1 - 1 / (2007 : ℚ)) ⟨by norm_num, by norm_num⟩
  have h3 := hf (1 - 1 / (1 - 1 / (2007 : ℚ))) ⟨by norm_num, by norm_num⟩
  norm_num [log_div, log_abs] at h1 h2 h3 ⊢
  linarith