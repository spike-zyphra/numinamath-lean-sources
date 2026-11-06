import Mathlib
open Set

/- Given the inequality $ax^{2}+5x+b > 0$ with the solution set $\{x|2 < x < 3\}$, find the solution set of the inequality $bx^{2}-5x+a > 0$. -/
theorem algebra_9070 (a b : ℝ) (ha : a ≠ 0) (h : ∀ x, a * x ^ 2 + 5 * x + b > 0 ↔ 2 < x ∧ x < 3) :
    ∀ x, b * x ^ 2 - 5 * x + a > 0 ↔ -1 / 2 < x ∧ x < -1 / 3 := by
  -- Set f(x) = ax^2 + 5x + b
  let f x := a * x ^ 2 + 5 * x + b
  -- f is continuous
  have fcont : Continuous f := by continuity
  -- Rewrite the hypothesis h as f⁻¹'(0, ∞) = (2, 3)
  replace h : f ⁻¹' (Ioi 0) = Ioo 2 3 := by
    ext x
    simp [h]
  -- Use the lemma from topology: the frontier of the preimage of a continuous function is contained in the preimage of the frontier
  have h0 := Continuous.frontier_preimage_subset fcont (Ioi 0)
  simp [h, show 2 < (3 : ℝ) by norm_num] at h0
  -- Simplify h0 and we get {2, 3} ⊆ f⁻¹' {0}
  -- Thus f(2) = f(3) = 0
  have h1 : f 2 = 0 := by
    specialize @h0 2
    simp at h0
    exact h0
  have h2 : f 3 = 0 := by
    specialize @h0 3
    simp at h0
    exact h0

  -- Solve the equations, we get a = -1, b = -6
  change a * 2 ^ 2 + 5 * 2 + b = 0 at h1
  change a * 3 ^ 2 + 5 * 3 + b = 0 at h2
  have ⟨va, vb⟩ : a = -1 ∧ b = -6 := by constructor <;> linarith
  subst a b
  clear * -

  -- Solve the inequality bx^2 - 5x + a > 0 using nlinarith
  intro x
  constructor <;> intro h
  . constructor <;> nlinarith
  . nlinarith
