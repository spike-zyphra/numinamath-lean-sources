import Mathlib
open Set

/- What is the value of $c$ if $x\cdot(3x+1)<c$ if and only when $x\in \left(-\frac{7}{3},2\right)$? -/
theorem algebra_16134 (c : ℝ) :
    (∀ x, x * (3 * x + 1) < c ↔ x ∈ Ioo (-7 / 3) 2) ↔ c = 14 := by
  -- Prove both directions
  constructor <;> intro H
  . -- We prove that if the condition holds, then c = 14

    -- Rewrite the hypothesis H as f⁻¹' (Iio c) = (-7/3, 2)
    apply Set.ext at H
    let f (x : ℝ) := x * (3 * x + 1)
    have hf : Continuous f := by continuity
    change f ⁻¹' (Iio c) = Set.Ioo (-7 / 3) 2 at H

    -- Use the lemma from topology: the frontier of the preimage of a continuous function is contained in the preimage of the frontier
    have h0 := Continuous.frontier_preimage_subset hf (Iio c)

    -- Simplify h0 and we get {2, -7/3} ⊆ f⁻¹' {c}
    simp [H, show (-7 / 3 : ℝ) < 2 by norm_num] at h0

    -- Thus f(2) = c
    have h : f 2 = c := by
      specialize @h0 2
      simp at h0
      exact h0

    -- Plug in 2 and we get c = 14
    simp [f] at h
    norm_num at h
    exact h.symm

  . -- We prove that if c = 14, then the condition holds
    subst c
    intro x
    simp
    -- Solve a quadratic inequality
    constructor <;> intro h
    . constructor <;> nlinarith
    . nlinarith
