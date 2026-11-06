import Mathlib

theorem calculus_70072 {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hfg : ∀ x, x * g (f x) * deriv f (g x) * deriv g x =
    f (g x) * deriv g (f x) * deriv f x) (hf' : ∀ x, 0 ≤ f x) (hg' : ∀ x, 0 < g x)
    (hfg' : ∀ a, ∫ x in (0)..a, f (g x) = 1 - Real.exp (-2 * a) / 2) (hg'' : g (f 0) = 1) :
    g (f 4) = Real.exp (-16) := by
  have h0 := hfg' 0
  norm_num at h0
  all_goals
    all_goals linarith [Real.exp_pos 0]