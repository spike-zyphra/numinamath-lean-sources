import Mathlib

open Real Set

lemma lemma_1 (x : ℝ) (hx : x ∈ Icc 0 2) : 2 * x - x ^ 2 ≥ 0 := by
  have h1 : 0 ≤ x := hx.1
  have h2 : x ≤ 2 := hx.2
  have h3 : 2 * x - x ^ 2 = x * (2 - x) := by
    nlinarith
  rw [h3]
  have h4 : 0 ≤ 2 - x := by
    linarith
  apply mul_nonneg
  .
    linarith
  .
    linarith


theorem calculus_156760 : ∫ x in (0)..2, max (2 * x - x ^ 2) 0 = 4 / 3 := by
  have h1 : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 2 → 2 * x - x ^ 2 ≥ 0 := by
    intro x hx
    apply lemma_1 x hx

  have h2 : ∫ x in (0)..2, max (2 * x - x ^ 2) 0 = ∫ x in (0)..2, (2 * x - x ^ 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx2 : x ≥ 0 := by
      have h1 : x ∈ Set.Icc (0 : ℝ) 2 := by
        simpa using hx
      exact h1.1
    have hx3 : x ≤ (2 : ℝ) := by
      have h2 : x ∈ Set.Icc (0 : ℝ) 2 := by
        simpa using hx
      exact h2.2
    have h3 : 2 * x - x ^ 2 ≥ 0 := by
      apply h1 x
      constructor <;> try linarith
    have h4 : max (2 * x - x ^ 2) 0 = 2 * x - x ^ 2 := by
      rw [max_eq_left (by linarith)]
    simpa using h4
  rw [h2]
  norm_num [intervalIntegral.integral_const, mul_comm]