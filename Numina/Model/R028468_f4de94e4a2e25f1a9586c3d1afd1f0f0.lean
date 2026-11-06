import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21546 (p : ℝ → ℝ) (hp : p = λ x => (x^2 + x + 1)/(x^2 + 1)) :
    range p = Set.Icc (1 / 2) (3 / 2) := by
  ext y
  simp [hp, Set.mem_range, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- First, prove that if y in range p, then y in [1/2, 3/2].
    rintro ⟨x, hx⟩
    have h1 : x^2 + 1 > 0 := by
      nlinarith [sq_nonneg x]
    have h2 : 1 / 2 ≤ (x^2 + x + 1) / (x^2 + 1) := by
      apply (le_div_iff₀ h1).mpr
      nlinarith [sq_nonneg (x + 1)]
    have h3 : (x^2 + x + 1) / (x^2 + 1) ≤ 3 / 2 := by
      apply (div_le_iff₀ h1).mpr
      nlinarith [sq_nonneg (x - 1)]
    constructor <;> nlinarith [h2, h3]
  · -- Second, prove that if y in [1/2, 3/2], then y in range p.
    rintro ⟨hy1, hy2⟩
    by_cases h : y = 1
    · -- Case y = 1
      rw [h]
      use 0
      norm_num
    · -- Case y ≠ 1
      have h4 : y - 1 ≠ 0 := by
        intro h'
        apply h
        linarith
      have h7 : ∃ x : ℝ, (y - 1) * x ^ 2 - x + (y - 1) = 0 := by
        have h5 : (1 : ℝ) - 4 * (y - 1) * (y - 1) ≥ 0 := by
          nlinarith
        use (1 + Real.sqrt (1 - 4 * (y - 1) * (y - 1))) / (2 * (y - 1))
        field_simp [(show y - 1 ≠ 0 by intro h'; apply h4; linarith)]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        nlinarith
      rcases h7 with ⟨x, hx⟩
      have h8 : (x^2 + x + 1) / (x^2 + 1) = y := by
        have h9 : x^2 + 1 > 0 := by nlinarith [sq_nonneg x]
        field_simp [(show x^2 + 1 > 0 by nlinarith [sq_nonneg x])] at *
        nlinarith [sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1)]
      exact ⟨x, by linarith [h8]⟩