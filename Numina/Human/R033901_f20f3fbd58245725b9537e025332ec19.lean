import Mathlib
open Set

/- Given the solution set of the inequality $x^2 - mx - 6n < 0$ is $\{x|-3 < x < 6\}$, find the value of $m+n$. -/
theorem algebra_9118 (m n : ℝ) (h : {x | x ^ 2 - m * x - 6 * n < 0} = {x | -3 < x ∧ x < 6}) :
    m + n = 6 := by
  -- Set f(x) = x^2 - mx - 6n
  let f x := x ^ 2 - m * x - 6 * n
  -- f is continuous
  have fcont : Continuous f := by continuity
  -- Rewrite the hypothesis h as f⁻¹'(-∞, 0) = (-3, 6)
  change f ⁻¹' (Iio 0) = Ioo (-3) 6 at h
  -- Use the lemma from topology: the frontier of the preimage of a continuous function is contained in the preimage of the frontier
  have h0 := Continuous.frontier_preimage_subset fcont (Iio 0)
  -- Simplify h0 and we get {-3, 6} ⊆ f⁻¹' {0}
  simp [h, show -3 < (6 : ℝ) by norm_num] at h0
  -- Thus f(-3) = f(6) = 0
  have h1 : f (-3) = 0 := by
    specialize @h0 (-3 : ℝ)
    simp at h0
    exact h0
  have h2 : f 6 = 0 := by
    specialize @h0 (6 : ℝ)
    simp at h0
    exact h0
  -- Expand the definition of f and solve the equations
  change (-3) ^ 2 - m * (-3) - 6 * n = 0 at h1
  change 6 ^ 2 - m * 6 - 6 * n = 0 at h2
  linarith
