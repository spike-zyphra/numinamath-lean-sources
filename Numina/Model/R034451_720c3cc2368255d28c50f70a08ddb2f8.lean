import Mathlib

open Real

theorem calculus_191372 {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hfg : ∀ x, x * g (f x) * deriv f (g x) * deriv g x =
    f (g x) * deriv g (f x) * deriv f x) (hf' : ∀ x, f x ≥ 0) (hg' : ∀ x, g x > 0)
    (hfg' : ∀ a, ∫ x in (0)..a, f (g x) = 1 - exp (-2 * a) / 2) (hg'' : g (f 0) = 1) :
    g (f 4) = exp (-16) := by
  have h0 : (∫ x in (0)..(0 : ℝ), f (g x) ) = 1 - exp (-2 * (0 : ℝ) ) / 2 := hfg' 0
  norm_num at h0 
  all_goals 
    linarith [show (1 / 2 : ℝ) > 0 by norm_num, h0]