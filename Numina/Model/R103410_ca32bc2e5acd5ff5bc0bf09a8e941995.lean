import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_311420 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0)..a, 2 * π * (b ^ 2 * (1 - x ^ 2 / a ^ 2)) = 4 * π * a * b ^ 2 / 3 := by
  have h1 : ∫ x in (0)..a, 2 * π * (b ^ 2 * (1 - x ^ 2 / a ^ 2)) = 
        2 * π * b ^ 2 * ∫ x in (0)..a, (1 - x^2 / a^2) := by
    simp [intervalIntegral.integral_mul_const]
    <;> ring_nf <;> simp [mul_comm] <;> ring_nf <;> field_simp
    <;> ring
  rw [h1]
  have h2 : ∫ x in (0)..a, (1 - x^2 / a^2) = a - a / 3 := by
    norm_num
    field_simp
    ring_nf
    <;> norm_num
    <;> ring_nf <;> field_simp <;> ring
  rw [h2]
  ring_nf
  <;> field_simp <;> ring_nf <;> nlinarith