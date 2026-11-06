import Mathlib

/-Solve for $x$: $$81^{2x} = 27^{3x - 4}.$$-/
theorem algebra_10374 {x : ℝ}: (81:ℝ) ^ (2 * x) = 27 ^ (3 * x - 4) ↔ x = 12 := by
-- Break "iff"
  constructor
  · intro h
-- Rewrite $81$ and $27$ as a power of $3$
    rw [show (81:ℝ)=3^(4:ℝ) by norm_num, show (27:ℝ)=3^(3:ℝ) by norm_num] at h
    repeat rw [← Real.rpow_mul] at h
-- Use the property of log with base $3$ to solve for $x$
    apply_fun (fun x => Real.logb 3 x) at h
    repeat rw [Real.logb_rpow] at h
    ring_nf at h; apply_fun (fun t => t - x * 8) at h
    ring_nf at h; linarith; any_goals norm_num
-- Conversely, check that $x=12$ satisfies the equation
  intro; simp_all; ring