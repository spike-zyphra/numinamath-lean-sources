import Mathlib

/- The derivative of the function $f(x) = (2\pi x)^2$ is $f'(x) = \boxed{8\pi^2x}$. -/
theorem algebra_9144 {f : ℝ → ℝ} (hf : f = fun x => (2 * Real.pi * x) ^ 2) : deriv f = fun x => 8 * Real.pi ^ 2 * x := by
rw [hf]
ext x
have h1: deriv (fun x => (2*Real.pi*x)^2) x = deriv (fun x => x^2) (2*Real.pi*x) * deriv (fun x => 2*Real.pi*x) x := by
  -- using the chain rule.
  have ht1: (fun x => (2*Real.pi*x)^2) = (fun x => x^2) ∘ (fun x => 2*Real.pi*x) := rfl
  rw [ht1]
  rw [deriv.comp]
  simp
  have ht2: DifferentiableAt ℝ (fun x => 2 * Real.pi * x) x := by
    have h11: Differentiable ℝ (fun x => (x:ℝ)) := by simp
    have h12: Differentiable ℝ (fun x => 2*Real.pi*x) := Differentiable.const_mul h11 (2*Real.pi)
    exact h12 x
  simp [ht2]
rw [h1]
-- (x^2)'=2x and (2πx)'=2π, substitute back.
have h2: deriv (fun (x:ℝ) => x^2) = (fun x => 2*x) := by simp
have h3: deriv (fun x => 2*Real.pi*x) x = 2*Real.pi := by
  have: deriv (fun x => 2*Real.pi*x) x = (2*Real.pi) * deriv (fun x => x) x := deriv_const_mul_field (2 * Real.pi)
  simp [this]
rw [h2,h3]
simp
ring