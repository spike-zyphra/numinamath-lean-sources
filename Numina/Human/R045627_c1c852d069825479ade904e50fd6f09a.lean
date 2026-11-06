import Mathlib

open Real

/- [Example 2.4.2] For real numbers $x, y, z, w$ not all zero, if

$$

\frac{6 x y+5 y z+6 z w}{x^{2}+y^{2}+z^{2}+w^{2}} \leqslant f \text {, }

$$


find the minimum value of $f$. -/
theorem inequalities_253925 (f : ℝ) :
    (∀ x y z w : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) →
      (6 * x * y + 5 * y * z + 6 * z * w) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) ≤ f) ↔
    f ≥ 9 / 2 := by
  -- we first simplify the statement
  suffices ∀ (x y z w : ℝ), x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0 → (6 * x * y + 5 * y * z + 6 * z * w) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) ≤ 9/2 by
    constructor
    · intro h
      specialize h 1 1.5 1.5 1; norm_num at h; exact h
    · intro h x y z w hyp
      specialize this x y z w hyp
      linarith
  intro x y z w notAllZero
  -- now we need to show a generalized two variable amgm
  have hamgm: ∀x y α :ℝ, 0<α → 2*x*y ≤ α *x^2 + (1/α) * y^2 := by
    intro x y α hα
    suffices 0 ≤ α * x ^ 2 + 1 / α * y ^ 2 - 2 * x * y by linarith
    rw [show α * x ^ 2 + 1 / α * y ^ 2 - 2 * x * y = (√α * x - 1/√α * y)^2 by ring_nf; rw [sq_sqrt (by linarith), show (√α)⁻¹ ^ 2 = (√α)⁻¹ ^ (2:ℝ) by norm_cast,Real.inv_rpow (by exact sqrt_nonneg α),show √α ^ (2:ℝ) = √α ^ (2:ℕ) by norm_cast,sq_sqrt (by linarith),show x * y * √α * (√α)⁻¹ * 2 = 2 * x * y * (√α * (√α)⁻¹) by ring_nf,mul_inv_cancel₀ (by exact sqrt_ne_zero'.mpr hα),mul_one]; ring_nf]
    nlinarith
  -- use this to go ahead and calculate
  conv_lhs =>
    calc _
    _ = 1/2 * (6 * (2*x * y) + 5 * (2*y * z) + 6 * (2 * z * w)) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring_nf
  have h1: ∀α β γ:ℝ, 0<α ∧ 0<β ∧ 0<γ → 1/2 * (6 * (2*x * y) + 5 * (2*y * z) + 6 * (2 * z * w)) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) ≤ 1/2 * (6 * (α*x^2+1/α *y^2) + 5 *(β*y^2+1/β *z^2) + 6 * (γ*z^2+1/γ *w^2)) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
    intro α β γ hαβγ
    gcongr
    exact hamgm x y α (by linarith)
    exact hamgm y z β (by linarith)
    exact hamgm z w γ (by linarith)
  conv at h1 =>
    intro α β γ h
    rhs; lhs; rhs;
    calc _
    _ = 6*α*x^2 + (5*β+6/α)*y^2 + (6*γ+5/β)*z^2 + 6/γ * w^2 := by ring_nf
  -- if we choose the correct α, β, γ so that all of the coefficiencts will be equal, the rhs will cancel out and we'll solve the problem
  -- the system is: 6*α = 5*β+6/α ∧ 5*β+6/α = 6*γ+5/β ∧ 6*γ+5/β = 6/γ
  -- we can see that α = 3/2, β =1 and γ = 2/3 is a solution, let's plug it into h1
  specialize h1 (3/2) 1 (2/3)
  norm_num at h1
  -- as expected we can now finish the problem
  conv_rhs at h1 =>
    calc _
    _ = 9 / 2 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring_nf
    _ = 9/2 := by rw [← mul_div, div_self (by
      intro h
      have h₁ : x = 0 := by nlinarith
      have h₂ : y = 0 := by nlinarith
      have h₃ : z = 0 := by nlinarith
      have h₄ : w = 0 := by nlinarith
      aesop), mul_one];
  exact h1