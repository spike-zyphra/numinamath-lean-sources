import Mathlib

theorem algebra_272769 {a b : ℝ} (ha : a = ⌊(2 + Real.sqrt 2) / (2 - Real.sqrt 2)⌋)
    (hb : 1 - b = (2 + Real.sqrt 2) / (2 - Real.sqrt 2) - a) :
    ((b - 1) * (5 - b)) / Real.sqrt (a^2 - 3^2) = -1 := by

  have h1 : (2 + Real.sqrt 2) / (2 - Real.sqrt 2) = 3 + 2 * Real.sqrt 2 := by
    have h2 : (2 - Real.sqrt 2) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    field_simp [h2, mul_comm]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

  have h2 : ⌊(2 + Real.sqrt 2) / (2 - Real.sqrt 2)⌋ = 5 := by
    rw [h1]
    have h3 : 5 < (3 + 2 * Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h4 : (3 + 2 * Real.sqrt 2 : ℝ) < 6 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith

  have ha2 : a = (5 : ℝ) := by
    rw [ha]
    exact_mod_cast h2

  have hb2 : b = (3 - 2 * Real.sqrt 2 : ℝ) := by
    rw [h1] at hb
    rw [show (a : ℝ) = (5 : ℝ) by linarith [ha2] ] at hb
    nlinarith

  have h3 : Real.sqrt (a^2 - 3^2) = (4 : ℝ) := by
    rw [ha2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  rw [h3, hb2]
  field_simp
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]