import Mathlib

open intervalIntegral

/-Find the area of the region bounded by the graphs of $y=x^{2}, y=x$, and $x=2$.-/
theorem calculus_608391 : ∫ x in (0 : ℝ)..2, |x ^ 2 - x| = 1 := by
-- We need to break the integral into two parts because $x^2-x$ changes sign at $x=1$
-- In order to use `integral_add_adjacent_intervals`, we need the following two integrable statements
  have II1 : IntervalIntegrable (fun x => |x ^ 2 - x|) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; continuity
  have II2 : IntervalIntegrable (fun x => |x ^ 2 - x|) MeasureTheory.volume 1 2 := by
    apply Continuous.intervalIntegrable; continuity
-- Prove that in the first half of the region, $x^2-x<=0$
  have EQ1 : Set.EqOn (fun (x : ℝ) => |x ^ 2 - x|) (fun x => x - x ^ 2) (Set.uIcc 0 1) := by
    intro x hx; simp at hx; simp; rw [abs_eq_neg_self.mpr]; ring
    rw [sub_nonpos, ← sub_nonneg, pow_two, ← mul_one_sub]; apply mul_nonneg
    all_goals linarith
-- Prove that in the second half of the region, $x^2-x>=0$
  have EQ2 : Set.EqOn (fun (x : ℝ) => |x ^ 2 - x|) (fun x => x ^ 2 - x) (Set.uIcc 1 2) := by
    intro x hx; simp at hx; simp
    rw [← sub_nonneg, pow_two, ← mul_sub_one]; apply mul_nonneg
    all_goals linarith
-- Apply `integral_add_adjacent_intervals` and `integral_congr` to compute the result
  rw [← integral_add_adjacent_intervals II1 II2, integral_congr EQ1]
  rw [integral_congr EQ2]; simp; norm_num
