import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Real

/- \section*{Exercise 6 - 261036}

Prove that for every real number $x>1$ the inequalities
$$
\frac{3}{2}\left(\sqrt[3]{(x+1)^{2}}-\sqrt[3]{x^{2}}\right)<\frac{1}{\sqrt[3]{x}}<\frac{3}{2}\left(\sqrt[3]{x^{2}}-\sqrt[3]{(x-1)^{2}}\right)
$$
hold! -/

theorem inequalities_190411 (x : ℝ) (hx : 1 < x) :
    3 / 2 * ((x + 1) ^ ((2 : ℝ) / 3) - x ^ ((2 : ℝ) / 3)) < 1 / x ^ ((1 : ℝ) / 3) ∧
    1 / x ^ ((1 : ℝ) / 3) < 3 / 2 * (x ^ ((2 : ℝ) / 3) - (x - 1) ^ ((2 : ℝ) / 3)) := by
  -- Rewrite the given to look like Bernoulli
  suffices 3/2 * ((1 + 1/x)^(2/3 : ℝ) - 1) < 1/x ∧ 1/x < 3/2 * (1 - (1 - 1/x)^(2/3 : ℝ)) by
    rcases this with ⟨lb, ub⟩
    constructor
      -- Multiply by x^(2/3) on both sides
    · rw [← mul_lt_mul_left (show 0 < x^(2/3 : ℝ) by positivity), ← mul_assoc, mul_comm _ (3/2), mul_assoc, mul_sub, mul_one, ← mul_rpow (by positivity) (by positivity)] at lb
      nth_rw 2 [one_div] at lb
      rw [← rpow_neg_one, ← rpow_add (by positivity), mul_add, mul_one, mul_div_cancel₀ _ (by positivity)] at lb
      norm_num at lb
      rw [one_div, ← rpow_neg (by positivity)]
      exact lb
    -- Multiply by x^(2/3) on both sides
    have : 1/x < 1 := by
      nth_rw 2 [show (1 : ℝ) = 1/1 by simp]
      exact one_div_lt_one_div_of_lt (by positivity) (hx)
    rw [← mul_lt_mul_left (show 0 < x^(2/3 : ℝ) by positivity), ← mul_assoc, mul_comm _ (3/2), mul_assoc, mul_sub, mul_one, ← mul_rpow (by positivity) (by linarith)] at ub
    nth_rw 2 [one_div] at ub
    rw [← rpow_neg_one, mul_sub x, mul_one] at ub
    nth_rw 5 [← rpow_one x] at ub
    rw [← rpow_add (by positivity), one_div, ← rpow_neg_one, ← rpow_add (by positivity)] at ub
    rw [one_div, ← rpow_neg (by positivity)]
    norm_num at ub
    exact ub
  constructor
  -- Use Bernoulli's inequality with exponent 2/3
  · have bernoulli : (1 + 1/x)^(2/3 : ℝ) < 1 + (2/3) * (1/x) := by
      apply rpow_one_add_lt_one_add_mul_self
      -- Check conditions
      trans 0
      all_goals
        try positivity
        try linarith
    linarith
  -- Use Bernoulli's inequality again, but with -(1/x)
  have bernoulli : (1 + -(1/x))^(2/3 : ℝ) < 1 + (2/3) * -(1/x) := by
    rw [neg_div']
    apply rpow_one_add_lt_one_add_mul_self
    -- Check conditions
    rw [le_div_iff₀ (by positivity)]
    all_goals
      try positivity
      try linarith
  rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at bernoulli
  linarith