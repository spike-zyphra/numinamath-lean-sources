import Mathlib

open Real
/-Let $x,$ $y,$ $z$ be real numbers such that $x + y + z = 1,$ and $x \ge -\frac{1}{3},$ $y \ge -1,$ and $z \ge -\frac{5}{3}.$  Find the maximum value of
\[\sqrt{3x + 1} + \sqrt{3y + 3} + \sqrt{3z + 5}.\]-/
theorem algebra_10836 : IsGreatest {t | ∃ x y z : ℝ, -1/3 ≤ x ∧ -1 ≤ y ∧ -5/3 ≤ z ∧ x + y + z = 1 ∧
t = sqrt (3 * x + 1) + sqrt (3 * y + 3) + sqrt (3 * z + 5)} 6 := by
-- Rewrite the goal and introduce assumptions
  rw [IsGreatest, upperBounds]; simp; constructor
-- Check that when $x$ is $1$, $y$ is $1/3$ and $z$ is $-1/3$, the value of the expression in question can reach $6$
  · use 1; norm_num; use 1/3; norm_num; use -1/3; norm_num
    rw [show (4:ℝ)=2*2 by norm_num, sqrt_mul_self]; any_goals norm_num
-- Prove the expression in question is always less or equal to $6$
  intro t x hx y hy z hz h ht
-- In order to apply Cauchy-Schwarz inequality, we introduce two auxillary vectors $A$, $B$ in three-dimensional Euclidean space
  let A : EuclideanSpace ℝ (Fin 3) := fun i => 1
  let B : EuclideanSpace ℝ (Fin 3) := fun i => if i = 0 then sqrt (3 * x + 1)
  else if i = 1 then sqrt (3 * y + 3) else sqrt (3 * z + 5)
-- Prove the inner product of $A$ and $B$ is $t$
  have inneq : inner A B = t := by
    simp [A, B, ht]; rw [Finset.sum_fin_eq_sum_range, Nat.range_eq_Icc_zero_sub_one]
    norm_num; repeat rw [← Nat.Icc_insert_succ_right, Finset.sum_insert]
    norm_num; split_ifs; all_goals simp_all
    ring
-- Compute the norms of $A$ and $B$
  have nA : ‖A‖ = sqrt 3 := by simp [A]; rw [EuclideanSpace.norm_eq]; norm_num
  have nB : ‖B‖ = sqrt 12 := by
    simp [B]; rw [EuclideanSpace.norm_eq]; norm_num
    rw [Finset.sum_fin_eq_sum_range, Nat.range_eq_Icc_zero_sub_one]
    norm_num; repeat rw [← Nat.Icc_insert_succ_right, Finset.sum_insert]
    norm_num; split_ifs; all_goals simp_all
    repeat rw [pow_two, ← sqrt_mul, sqrt_mul_self]
    rw [show 3*z+5+(3*y+3+(3*x+1))=3*(x+y+z)+9 by ring, h]; norm_num
    any_goals linarith
-- Apply Cauchy-Schwarz inequality and simpify the norms using nA and nB
  have CSAB := real_inner_le_norm A B
  rw [nA, nB, inneq, ← sqrt_mul, show (3:ℝ)*12=6*6 by norm_num, sqrt_mul_self] at CSAB
  assumption; any_goals norm_num