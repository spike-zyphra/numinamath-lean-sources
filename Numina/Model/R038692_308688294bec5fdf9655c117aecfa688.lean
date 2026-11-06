import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_215868 (f : ℝ → ℝ) (hf : f = λ x => 2^(x^2 - 4*x + 1)) :
    range f = {y | 1/8 ≤ y} := by
  ext y
  simp [hf, mem_range]
  constructor
  · -- Prove ⊆, i.e., if y in range f, then y ≥ 1/8.
    intro hy
    rcases hy with ⟨x, hx⟩
    have h1 : x ^ 2 - 4 * x + 1 ≥ -3 := by
      nlinarith [sq_nonneg (x - 2)]
    have h2 : (2 : ℝ) ^ (x ^ 2 - 4 * x + 1) ≥ (2 : ℝ) ^ (-3 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      all_goals linarith
    have h3 : (2 : ℝ) ^ (-3 : ℝ) = (1 : ℝ) / 8 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast, pow_succ]
    have eq1 : (2 : ℝ) ^ (x ^ 2 - 4 * x + 1) = y := by
      linarith [hx]

    have ineq : (2 : ℝ) ^ (x ^ 2 - 4 * x + 1) ≥ (1 : ℝ) / 8 := by
      calc
        (2 : ℝ) ^ (x ^ 2 - 4 * x + 1) ≥ (2 : ℝ) ^ (-3 : ℝ) := by
          exact h2
        _ = (1 / 8 : ℝ) := by
          rw [h3]
          all_goals norm_num  -- clean up to avoid equality gap

    linarith [eq1, ineq]

  · -- Prove ⊇, i.e., if y ≥ 1/8, then there exists an x such that f(x) = y.
    intro hy
    have h4 : 0 ≤ (3 + Real.logb (2 : ℝ) y) := by
      have h5 : Real.logb (2 : ℝ) y ≥ Real.logb (2 : ℝ) (1 / 8) := by
        apply Real.logb_le_logb_of_le
        all_goals
          nlinarith [hy]
      have h6 : Real.logb (2 : ℝ) (1 / 8) = -3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      nlinarith [h5, h6]

    use 2 + Real.sqrt (3 + Real.logb (2 : ℝ) y)
    have h_eq : (2 + Real.sqrt (3 + Real.logb (2 : ℝ) y)) ^ 2 - 4 * (2 + Real.sqrt (3 + Real.logb (2 : ℝ) y)) + 1 = Real.logb (2 : ℝ) y := by
      nlinarith [Real.sq_sqrt (h4), Real.sqrt_nonneg (3 + Real.logb (2 : ℝ) y)]

    rw [show (2 : ℝ) ^ ((2 + Real.sqrt (3 + Real.logb (2 : ℝ) y)) ^ 2 - 4 * (2 + Real.sqrt (3 + Real.logb (2 : ℝ) y)) + 1) = (2 : ℝ) ^ (Real.logb (2 : ℝ) y) by rw [h_eq]]
    
    rw [Real.rpow_logb]
    all_goals
      nlinarith [hy]
  all_goals try tauto
  all_goals try linarith