import Mathlib

open Real
open scoped BigOperators

theorem inequalities_277735 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 + 4 * a * b * c > a ^ 3 + b ^ 3 + c ^ 3 ∧
  2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 > a ^ 4 + b ^ 4 + c ^ 4 ∧
  2 * a * b + 2 * b * c + 2 * c * a > a ^ 2 + b ^ 2 + c ^ 2 := by
  constructor
  · -- Prove the first inequality: a * (b - c)² + b * (c - a)² + c * (a - b)² + 4 * a * b * c > a³ + b³ + c³
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')]
  constructor
  · -- Prove the second inequality: 2 * a² * b² + 2 * b² * c² + 2 * c² * a² > a⁴ + b⁴ + c⁴
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')]
  · -- Prove the third inequality: 2 * a * b + 2 * b * c + 2 * c * a > a² + b² + c²
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')]