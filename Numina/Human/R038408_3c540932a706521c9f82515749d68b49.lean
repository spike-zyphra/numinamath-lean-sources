import Mathlib

open Real Set
open scoped BigOperators

/- Find the minimum value of the function \[f(x) = \sqrt{-x^2 + 4x + 21} - \sqrt{-x^2 + 3x + 10}.\] -/
theorem algebra_22143 :
  IsLeast {y : ℝ | ∃ x, 0 ≤ -x^2 + 4 * x + 21 ∧ 0 ≤ -x^2 + 3 * x + 10 ∧ y = sqrt (-x^2 + 4 * x + 21) - sqrt (-x^2 + 3 * x + 10)} (sqrt 2) := by
  -- The domain of $f$ is $[-2, 5]$
  have domaineq : ∀ x : ℝ, (0 ≤ -x^2 + 4 * x + 21 ∧ 0 ≤ -x^2 + 3 * x + 10) → (-2 ≤ x ∧ x ≤ 5) := by
    intro x hx
    have le := hx.2
    have eq : -x ^ 2 + 3 * x + 10 = (5 - x) * (2 + x) := by
      ring
    rw [eq] at le
    rcases mul_nonneg_iff.mp le with le2 | le2
    constructor
    linarith
    linarith
    linarith
  constructor
  · -- When $x = 1 / 3, f(x) = \sqrt{2}$
    use 1 / 3
    constructor
    -- $1 / 3 \in [-2, 5]$
    linarith
    constructor
    linarith
    norm_num
    have eq : √2 = √(2 * 10 ^ 2) / √(3 ^ 2) - √(2 * 7 ^ 2) / √(3 ^ 2) := by
      rw [sqrt_mul (by exact zero_le_two), sqrt_mul (by exact zero_le_two), sqrt_sq (by exact Nat.ofNat_nonneg' 10), sqrt_sq (by exact zero_le_three), sqrt_sq (by exact Nat.ofNat_nonneg' 7)]
      ring
    rw [eq]
    ring_nf
  · -- $f(x) \ge \sqrt{2}$ for all $x$
    intro y hy
    rcases hy with ⟨x, hxle1, hxle2, hy⟩
    have xin := domaineq x ⟨hxle1, hxle2⟩
    -- $f(x) = \sqrt{(7 - x)(3 + x)} - \sqrt{(5 - x)(2 + x)$
    have yeq : y = √((7 - x) * (3 + x)) - √((5 - x) * (2 + x)) := by
      rw [hy]
      ring_nf
    -- $0 < f(x)$
    have ygt : 0 < y := by
      rw [yeq]
      apply sub_pos_of_lt
      apply Real.sqrt_lt_sqrt
      refine mul_nonneg_iff.mpr ?_
      left
      constructor
      linarith
      linarith
      nlinarith
    -- $f^2(x) \geq 2$
    have yge : 2 ≤ y ^ 2 := by
      have nonneg1 : 0 ≤ (7 - x) * (3 + x) := by
        refine mul_nonneg_iff.mpr ?_
        left
        constructor
        linarith
        linarith
      have nonneg2 : 0 ≤ (5 - x) * (2 + x) := by
        refine mul_nonneg_iff.mpr ?_
        left
        constructor
        linarith
        linarith
      have nonneg3 : 0 ≤ (7 - x) * (2 + x) := by
        refine mul_nonneg_iff.mpr ?_
        left
        constructor
        linarith
        linarith
      have nonneg4 : 0 ≤ (5 - x) * (3 + x) := by
        refine mul_nonneg_iff.mpr ?_
        left
        constructor
        linarith
        linarith
      -- $[f(x)]^2 = 2 + \left[ \sqrt{(7 - x)(2 + x)} - \sqrt{(5 - x)(3 + x)} \right]^2$
      have eq : y ^ 2 = 2 + (√((7 - x) * (2 + x)) - √((5 - x) * (3 + x))) ^ 2 := by
        rw [yeq, sub_pow_two, sq_sqrt nonneg1, sq_sqrt nonneg2, mul_assoc, ← sqrt_mul nonneg1, sub_pow_two, sq_sqrt nonneg3, sq_sqrt nonneg4, mul_assoc 2, ← sqrt_mul nonneg3]
        ring_nf
      rw [eq]
      have ge : 0 ≤ (√((7 - x) * (2 + x)) - √((5 - x) * (3 + x))) ^ 2 := by
        exact sq_nonneg (√((7 - x) * (2 + x)) - √((5 - x) * (3 + x)))
      linarith
    -- So $f(x) ≥ 2$
    have eq2 : y = √(y ^ 2) := by
      refine Eq.symm (sqrt_sq ?_)
      exact le_of_lt ygt
    rw [eq2]
    apply sqrt_le_sqrt
    exact yge