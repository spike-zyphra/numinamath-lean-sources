import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- 20th Putnam 1959 Problem A4 R is the reals. f, g : [0, 1] → R are arbitary functions. Show that we can find x, y such that |xy - f(x) - g(y)| ≥ 1/4. -/
theorem inequalities_138732 (f g : ℝ → ℝ) :
  ∃ (x y : ℝ), x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧ |x * y - f x - g y| ≥ 1 / 4 := by
  -- Use a proof by contradiction
  by_contra h
  push_neg at h
  -- Use the given for the four corners of a square
  have f1 : |f 0 + g 0| < 1/4 := by
    have : |0 * 0 - f 0 - g 0| < 1/4 := h 0 0 (by norm_num) (by norm_num)
    norm_num at this
    rw [sub_eq_add_neg, ← neg_add, abs_neg] at this
    exact this
  have f2 : |f 1 + g 0| < 1/4 := by
    have : |1 * 0 - f 1 - g 0| < 1/4 := h 1 0 (by norm_num) (by norm_num)
    norm_num at this
    rw [sub_eq_add_neg, ← neg_add, abs_neg] at this
    exact this
  have f3 : |f 0 + g 1| < 1/4 := by
    have : |0 * 1 - f 0 - g 1| < 1/4 := h 0 1 (by norm_num) (by norm_num)
    norm_num at this
    rw [sub_eq_add_neg, ← neg_add, abs_neg] at this
    exact this
  have f4 : |1 - f 1 - g 1| < 1/4 := by
    have : |1 * 1 - f 1 - g 1| < 1/4 := h 1 1 (by norm_num) (by norm_num)
    rw [mul_one] at this
    exact this
  -- Use f1, f2, f3 to derive a contradiction to f4
  have f5 : |1 - f 1 - g 1| ≥ 1/4 := by
    have : f 1 + g 1 ≤ 3/4 := by
      calc
        f 1 + g 1 = f 1 + g 0 + f 0 + g 1 - (f 0 + g 0) := by linarith
        _ ≤ |f 1 + g 0| + |f 0 + g 1| - (f 0 + g 0) := by linarith [le_abs_self (f 1 + g 0), le_abs_self (f 0 + g 1)] -- Use triangle inequality
        _ ≤ |f 1 + g 0| + |f 0 + g 1| + |f 0 + g 0| := by linarith [neg_le_abs (f 0 + g 0)]
        _ ≤ 3/4 := by linarith
    have : 1 - f 1 - g 1 ≥ 1/4 := by linarith
    calc
      |1 - f 1 - g 1| ≥ 1 - f 1 - g 1 := by linarith [le_abs_self (1 - f 1 - g 1)]
      _ ≥ 1/4 := this
  linarith