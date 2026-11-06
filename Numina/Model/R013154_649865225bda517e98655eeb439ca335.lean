import Mathlib

/- If the equation ${{x}^{2}}+ax+b-3=0\left( a,b\in \mathbf{R} \right)$ has real roots in the interval $\left[ 1,2 \right]$, then the minimum value of ${{a}^{2}}+{{\left( b-4 \right)}^{2}}$ is ___        ___. -/
theorem algebra_11191 (a b : ℝ) (h : ∃ x₁ x₂ : ℝ, x₁ ∈ Set.Icc 1 2 ∧ x₂ ∈ Set.Icc 1 2 ∧
    x₁^2 + a * x₁ + b - 3 = 0 ∧ x₂^2 + a * x₂ + b - 3 = 0) :
    a^2 + (b - 4)^2 ≥ 2 := by 
  rcases h with ⟨x₁, x₂, hx₁, hx₂, heq₁, heq₂⟩
  rcases hx₁ with ⟨hx₁l, hx₁u⟩
  rcases hx₂ with ⟨hx₂l, hx₂u⟩
  nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 3), sq_nonneg (x₁ - 1), sq_nonneg (x₂ - 1), 
          sq_nonneg (x₁ - x₂), 
          mul_nonneg (sub_nonneg.mpr hx₁l) (sub_nonneg.mpr hx₁u), 
          mul_nonneg (sub_nonneg.mpr hx₂l) (sub_nonneg.mpr hx₂u)]