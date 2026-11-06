import Mathlib

open Real Set


theorem inequalities_268552 (a : ℝ) :
    (∀ x : ℝ, |x - 2 * a| + |2 * x - a| ≥ a ^ 2) ↔
    a ∈ Icc (-3 / 2) (3 / 2) := by
  constructor
  ·
    intro h
    have h1 := h (a / 2)
    have h2 : 3 * |a| / 2 ≥ a ^ 2 := by
      have h2 : |a / 2 - 2 * a| + |2 * (a / 2) - a| ≥ a ^ 2 := by
        simpa using h1
      have h3 : |a / 2 - 2 * a| = 3 * |a| / 2 := by
        have h4 : a / 2 - 2 * a = -3 * a / 2 := by ring
        rw [h4]
        have h5 : |-3 * a / 2| = 3 * |a| / 2 := by
          calc
            |-3 * a / 2| = |(-3 / 2) * a| := by ring_nf
            _ = |(-3 / 2)| * |a| := by rw [abs_mul]
            _ = (3 / 2) * |a| := by norm_num [abs_neg]
            _ = 3 * |a| / 2 := by ring_nf
        linarith
      have h4 : |2 * (a / 2) - a| = (0 : ℝ) := by
        have h5 : 2 * (a / 2) - a = (0 : ℝ) := by ring
        rw [h5]
        simp
      rw [h3, h4] at h2
      linarith
    have h3 : a ≤ 3 / 2 := by
      by_cases ha : a ≥ 0
      ·
        rw [abs_of_nonneg ha] at h2
        nlinarith [sq_nonneg (a - 3 / 2)]
      ·
        have h4 : a < 0 := lt_of_not_ge ha
        rw [abs_of_neg h4] at h2
        nlinarith [sq_nonneg (a - 3 / 2)]
    have h4 : -3 / 2 ≤ a := by
      by_cases ha : a ≥ 0
      ·
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (a + 3 / 2)]
      ·
        have h5 : a < 0 := lt_of_not_ge ha
        rw [abs_of_neg h5] at h2
        nlinarith [sq_nonneg (a + 3 / 2), sq_nonneg (a - 3 / 2)]
    exact ⟨h4, h3⟩
  ·
    rintro ⟨h1, h2⟩
    intro x
    by_cases ha : a ≥ 0
    ·
      by_cases h : x ≥ 2 * a
      ·
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (x - 2 * a)]
      ·
        by_cases h' : x ≥ a / 2
        ·
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (x - a / 2)]
        ·
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (x - a / 2)]
    ·
      have h_neg : a < 0 := by linarith
      by_cases h : x ≥ a / 2
      ·
        rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
        nlinarith [sq_nonneg (a + 3 / 2), sq_nonneg (x - a / 2)]
      ·
        by_cases h' : x ≥ 2 * a
        ·
          rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by nlinarith)]
          nlinarith [sq_nonneg (a + 3 / 2), sq_nonneg (x - 2 * a)]
        ·
          rw [abs_of_nonpos (by nlinarith), abs_of_nonpos (by nlinarith)]
          nlinarith [sq_nonneg (a + 3 / 2), sq_nonneg (x - 2 * a)]