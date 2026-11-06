import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_295337 :
  IsGreatest {a | ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → a * (x + y + z) ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 + y * z} (3 / 7) ∧
  IsLeast {b | ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x ^ 2 + y ^ 2 + z ^ 2 + y * z ≤ b * (x + y + z) ^ 2} 1 := by

  constructor
  · -- Show that 3/7 is greatest in the set {a | ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → a * (x + y + z) ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 + y * z}
    constructor
    · -- Show 3/7 is in the set
      intro x y z hx hy hz
      have h1 : (x + y + z : ℝ) ≥ 0 := by
        linarith
      have h2 : (3 / 7 : ℝ) * (x + y + z) ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 + y * z := by
        nlinarith [sq_nonneg (x - 3 / 7 * (x + y + z)), sq_nonneg (y - 2 / 7 * (x + y + z)), sq_nonneg (z - 2 / 7 * (x + y + z)), 
            mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz]
      linarith
    · -- Show 3/7 is the greatest
      intro a ha
      have h1 := ha (3 / 7 : ℝ) (2 / 7 : ℝ) (2 / 7 : ℝ) (by norm_num) (by norm_num) (by norm_num)
      norm_num at h1
      nlinarith
  · -- Show that 1 is least in the set {b | ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x ^ 2 + y ^ 2 + z ^ 2 + y * z ≤ b * (x + y + z) ^ 2}
    constructor
    · -- Show 1 is in the set 
      intro x y z hx hy hz
      have h1 : (x + y + z : ℝ) ≥ 0 := by
        linarith
      have h2 : x ^ 2 + y ^ 2 + z ^ 2 + y * z ≤ 1 * (x + y + z) ^ 2 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
            mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz]
      nlinarith
    · -- Show 1 is the least such number
      intro b hb
      have h1 := hb 1 0 0 (by norm_num) (by norm_num) (by norm_num)
      norm_num at h1
      nlinarith