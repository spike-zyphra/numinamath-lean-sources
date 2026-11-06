import Mathlib

open Real

theorem calculus_228946 {f g : ℝ → ℝ} (x₀ : ℝ) (hf : DifferentiableAt ℝ f x₀) (hg : DifferentiableAt ℝ g x₀) :
    deriv (fun x => f x + g x) x₀ = deriv f x₀ + deriv g x₀ ∧
    deriv (fun x => f x * g x) x₀ = deriv f x₀ * g x₀ + f x₀ * deriv g x₀ ∧
    g x₀ ≠ 0 → deriv (fun x => f x / g x) x₀ = (deriv f x₀ * g x₀ - f x₀ * deriv g x₀) / (g x₀)^2 := by 
  intro h
  rcases h with ⟨h1, h2, hg_ne_zero⟩
  have h3 : deriv (fun (x : ℝ) => f x / g x) x₀ = (deriv f x₀ * g x₀ - f x₀ * deriv g x₀) / (g x₀) ^ 2 := by
    apply deriv_div
    all_goals
      try exact hf
      try exact hg
      try exact hg_ne_zero
  exact h3