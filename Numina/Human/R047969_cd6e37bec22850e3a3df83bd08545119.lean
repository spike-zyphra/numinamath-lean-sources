import Mathlib

/- The equation of the tangent line to $y=x\sin x$ at $x=\pi$ is __________. -/
theorem algebra_9024 (f : ℝ → ℝ) (hf : f = fun x => x * Real.sin x) : ∃ m c, ∀ x, x = Real.pi → (f x = m * x + c ∧ m = deriv f Real.pi ∧ c = f Real.pi - m * Real.pi) := by
-- we can prove the tangent line is y = π^2 - πx, so we use -π and π^2 here.
use (-Real.pi)
use Real.pi * Real.pi
intro x hx
have eq1: f x = -Real.pi * x + Real.pi * Real.pi := by
  simp [hf, hx]
-- find the derivative of the function, f'(x)=(x sin x)' = x' sinx + x*(sin x)' = sin x + x cos x.
-- and this f'(x) (here x = π) is slope of the tangent line (here we use -π)
have eq2: -Real.pi = deriv f Real.pi := by
  have ht1: deriv f Real.pi = deriv (fun x => x) Real.pi * Real.sin x + x * deriv Real.sin x := by
    let f1(x:ℝ):ℝ := x
    have ht1: deriv (fun x => f1 x * Real.sin x) x = deriv f1 x * Real.sin x + f1 x * deriv Real.sin x := by
      have hd1: DifferentiableAt ℝ f1 x := by
        have: HasDerivAt f1 1 x := hasDerivAt_id' x
        exact differentiableAt_id'
      have hd2: DifferentiableAt ℝ Real.sin x := Real.differentiableAt_sin
      apply deriv_mul hd1 hd2
    have ht2: deriv f x = deriv (fun x => f1 x * Real.sin x) x := congrFun (congrArg deriv hf) x
    rw [← hx]
    rw [ht2, ht1]
  rw [ht1]
  simp [hx]
-- substitute back to determine the whole equation of the tangent line
have eq3: Real.pi * Real.pi = f Real.pi - -Real.pi*Real.pi := by
  simp
  rw [hf]
  simp
exact ⟨eq1, eq2, eq3⟩