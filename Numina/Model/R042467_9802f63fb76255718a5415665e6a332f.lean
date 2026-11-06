import Mathlib

theorem algebra_18612 : {a : ℝ | ∃ x, x^2 + a = a * x} = Set.Iic 0 ∪ Set.Ici 4 := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  constructor
  · -- Assume there exists an x such that x^2 + a = a * x
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : (x - a / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h2 : a ^ 2 - 4 * a ≥ 0 := by
      nlinarith
    by_cases h3 : a ≤ 0
    · -- if $a \leq 0$ then $a \in (-\infty, 0]$
      left
      nlinarith
    · -- Assume a > 0 
      have h4 : a > 0 := by linarith
      have h5 : a ≥ 4 := by
        nlinarith [sq_nonneg (a - 4)]
      right
      linarith
  · -- Assume a ∈ (-∞, 0] ∪ [4, ∞)
    rintro (ha | ha)
    · -- Assume a ≤ 0 
      have h1 : a ≤ 0 := ha
      use (a + Real.sqrt (a ^ 2 - 4 * a)) / 2
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * a), Real.sq_sqrt (show (a ^ 2 - 4 * a) ≥ 0 by nlinarith)]
    · -- Assume a ≥ 4 
      have h1 : a ≥ 4 := ha
      use (a + Real.sqrt (a ^ 2 - 4 * a)) / 2
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * a), Real.sq_sqrt (show (a ^ 2 - 4 * a) ≥ 0 by nlinarith)]