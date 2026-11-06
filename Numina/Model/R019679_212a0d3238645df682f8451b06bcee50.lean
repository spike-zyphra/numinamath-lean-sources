import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_70476 {S : ℝ} (hS : S > 0) :
    IsGreatest {x | ∃ a b, a > 0 ∧ b > 0 ∧ a * b = S ∧ x = S / (2 * S + 2 * a + 2 * b + 2)} (S / (2 * (Real.sqrt S + 1)^2)) := by
  constructor 
  · -- We can achieve the value $\frac{S}{2(\sqrt{S} + 1)^2}$ with $a = \sqrt{S}$ and $b = \sqrt{S}$.
    use Real.sqrt S, Real.sqrt S
    constructor
    · -- Show that sqrt(S) > 0
      positivity
    constructor
    · -- Show that sqrt(S) > 0
      positivity
    constructor
    · -- Show that $(\sqrt{S}) \cdot (\sqrt{S}) = S$
      have h3 : Real.sqrt S * Real.sqrt S = S := by
        exact Real.mul_self_sqrt (show 0 ≤ (S : ℝ) by linarith)
      linarith
    · -- Verify that the value is equal to $\frac{S}{2(\sqrt{S} + 1)^2}$
      have h4 : 2 * S + 2 * Real.sqrt S + 2 * Real.sqrt S + 2 = 2 * (Real.sqrt S + 1)^2 := by
        nlinarith [Real.sqrt_nonneg S, Real.sq_sqrt (show (0 : ℝ) ≤ S by linarith)]
      rw [h4]
  · -- Show that $\frac{S}{2(\sqrt{S} + 1)^2}$ is an upper bound for all elements in the set.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hab, hx⟩
    have h1 : a * b = S := hab
    have h2 : a + b ≥ 2 * Real.sqrt S := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - Real.sqrt S),
        sq_nonneg (b - Real.sqrt S),
        Real.sqrt_nonneg S, Real.sq_sqrt (show (0 : ℝ) ≤ S by linarith)]
    have h3 : 2 * a + 2 * b ≥ 4 * Real.sqrt S := by
      nlinarith [h2]
    have h4 : 2 * S + 2 * a + 2 * b + 2 ≥ 2 * (Real.sqrt S + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg S, Real.sq_sqrt (show (0 : ℝ) ≤ S by linarith),
        h3, sq_nonneg (a - b),
        sq_nonneg (a - Real.sqrt S),
        sq_nonneg (b - Real.sqrt S)]
    have h5 : S / (2 * S + 2 * a + 2 * b + 2) ≤ S / (2 * (Real.sqrt S + 1)^2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith