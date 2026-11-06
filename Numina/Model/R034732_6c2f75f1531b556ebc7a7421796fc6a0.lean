import Mathlib

open Real Set
open scoped BigOperators


theorem algebra_9382 {f : ℝ → ℝ} (hf : f = λ x => exp x + x^3) :
  {x | f (x^2) < f (3 * x - 2)} = {x | 1 < x ∧ x < 2} := by
  ext x
  simp only [hf, Set.mem_setOf_eq]
  constructor
  · -- Assume f(x^2) < f(3 * x - 2), prove 1 < x ∧ x < 2
    intro h
    have h1 : exp (x^2) + (x^2)^3 < exp (3 * x - 2) + (3 * x - 2)^3 := by
      linarith
    by_cases h2 : x^2 ≥ (3 * x - 2)
    · -- If x^2 ≥ 3 * x - 2, then f(x^2) ≥ f(3 * x - 2), contradiction.
      have h3 : exp (x^2) ≥ exp (3 * x - 2) := by 
        apply Real.exp_le_exp_of_le 
        nlinarith
      have h4 : (x^2)^3 ≥ (3 * x - 2)^3 := by
        have h5 : x^2 ≥ (3 * x - 2 : ℝ) := h2
        nlinarith [sq_nonneg (x^2 - (3 * x - 2)), sq_nonneg (x^2 + (3 * x - 2)), sq_nonneg (x), sq_nonneg ((3 * x - 2))]
      have h6 : exp (x^2) + (x^2)^3 ≥ exp (3 * x - 2) + (3 * x - 2)^3 := by
        linarith [h3, h4]
      linarith
    · -- Since $x^2 < 3x - 2$, we have $1 < x < 2$
      have h2 : x^2 < (3 * x - 2) := by 
        linarith
      have h3 : 1 < x := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2)]
      have h4 : x < 2 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2)]
      exact ⟨h3, h4⟩
  · -- Assume 1 < x ∧ x < 2 prove f(x^2) < f(3 * x - 2)
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : x^2 < (3 * x - 2 : ℝ) := by 
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < x - 1 by linarith), sq_pos_of_pos (show (0 : ℝ) < 2 - x by linarith)]
    -- Now show $f(x^2) < f(3 * x - 2)$ using strict monotonicity of $f$
    have h4 : exp (x^2) < exp (3 * x - 2 : ℝ) := by 
      apply Real.exp_strictMono
      linarith
    -- Show $f(a) < f(b)$ given $a < b$ for $f(x)=x^3$
    have h5 : (x^2 : ℝ)^3 < (3 * x - 2 : ℝ)^3 := by
      have h6 : x^2 < (3 * x - 2 : ℝ) := by
        linarith
      -- Show $f(a) < f(b)$ given $a < b$ for $f(x)=x^3$
      nlinarith [sq_nonneg (x^2 - (3 * x - 2)), sq_nonneg (x^2 + (3 * x - 2)), sq_nonneg (x), sq_nonneg ((3 * x - 2))]
    -- Using strict monotonicity of $exp$ and $x^3$ to conclude $f(x^2) < f(3x - 2)$.
    have h6 : exp (x ^ 2) + (x^2)^3 < exp (3 * x - 2 : ℝ) + (3 * x - 2 : ℝ)^3 := by
      linarith [h4, h5]
    linarith