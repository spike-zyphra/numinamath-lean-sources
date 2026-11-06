import Mathlib

open Real

/-When you simplify $\sqrt[3]{24a^4b^6c^{11}}$, what is the sum of the exponents of the variables that are outside the radical?-/
theorem algebra_13921 (a b c : ℝ)(ha : 0 < a)(hb : 0 < b)(hc : 0 < c):
(24 * a ^ (4:ℝ) * b ^ (6:ℝ) * c ^ (11:ℝ)) ^ ((1:ℝ)/3) =
2 * a ^ (1:ℝ) * b ^ (2:ℝ) * c ^ (3:ℝ) * (3 * a * c ^ (2:ℝ)) ^ ((1:ℝ)/3) ∧ 1 + 2 + 3 = 6 := by
-- This is a straightforward simplification using varies real exponent rules like mul_rpow, rpow_mul and rpow_add
  constructor
  · repeat rw [mul_rpow]; repeat rw [← rpow_mul]; ring_nf
    have aux1: (24:ℝ)^((1:ℝ)/3)=2*3^((1:ℝ)/3) := by
      rw [show (24:ℝ)=2^(3:ℝ)*3 by norm_num, mul_rpow, ← rpow_mul]
      ring; any_goals norm_num
    have aux2 : a ^ ((4:ℝ)/3) = a * a ^ ((1:ℝ)/3) := by
      nth_rw 2 [show a=a^(1:ℝ) by simp]
      rw [← rpow_add]; field_simp; ring_nf
      assumption
    have aux3 : c ^ ((11:ℝ)/3) = c ^ (3:ℝ) * c ^ ((2:ℝ)/3) := by
      rw [← rpow_add]; field_simp; ring_nf
      assumption
    rw [rpow_one, aux1, aux2, aux3]; ring
    any_goals linarith
    apply rpow_nonneg; linarith
    apply mul_nonneg; linarith; apply rpow_nonneg; linarith
    any_goals apply rpow_nonneg; linarith
    apply mul_nonneg; any_goals apply rpow_nonneg; linarith
    apply mul_nonneg; apply mul_nonneg
    norm_num; any_goals apply rpow_nonneg; linarith
  norm_num