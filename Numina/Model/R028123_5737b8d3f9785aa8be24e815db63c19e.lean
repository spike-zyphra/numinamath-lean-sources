import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_297017 (m : ℝ) :
  (∀ a b, a ≤ -1 → b ≤ m → a * 2 ^ b - b - 3 * a ≥ 0) ↔ m ≤ 1 := by
  constructor
  · -- Assume that for all a, b with a <= -1 and b <= m, the inequality holds, prove m <= 1
    intro h
    by_contra h1
    push_neg at h1
    have h2 := h (-1 : ℝ) m (by norm_num) (by linarith)
    have h3 : (-1 : ℝ) * (2 : ℝ) ^ m - m - 3 * (-1) ≥ 0 := h2
    have h4 : m > (1 : ℝ) := h1
    have h5 : (2 : ℝ) ^ m > (3 - m : ℝ) := by
      have h41 : m > 1 := h4
      have h7 : (2 : ℝ) ^ m > (2 : ℝ) := by
        have h7 : (2 : ℝ) ^ m > (2 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h8 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
        rw [h8] at h7
        linarith
      nlinarith
    have h6 : (2 : ℝ) ^ m + m - (3 : ℝ) > 0 := by linarith
    nlinarith
  · -- Assume m ≤ 1, prove ∀ a b, a ≤ -1 → b ≤ m → a * 2 ^ b - b - 3 * a ≥ 0
    intro hm a b ha hb
    have h11 : b ≤ (1 : ℝ) := by linarith [hb, hm]
    have h12 : (2 : ℝ) ^ b ≤ (2 : ℝ) := by
      have h13 : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals linarith
      have h14 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
      rw [h14] at h13
      linarith
    nlinarith [sq_nonneg (b + 1), sq_nonneg (a + 1), Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by linarith) b, Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (show b ≤ (1 : ℝ) by linarith)]