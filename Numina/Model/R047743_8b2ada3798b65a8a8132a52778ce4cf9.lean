import Mathlib

open Real

theorem algebra_13225 {f g : ℝ → ℝ} (hf : f = fun x => 1 / (2 * x + b)) (hg : g = fun x => (1 - 2 * x) / (2 * x))
    (hfg : ∀ x, f (g x) = x ∧ g (f x) = x) :
    b = 2 := by

  have h1 := (hfg 1).1
  simp [hf, hg] at h1 
  norm_num at h1 
  have h3 : b = 2 := by
    linarith 
  exact h3