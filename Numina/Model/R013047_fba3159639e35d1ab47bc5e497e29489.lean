import Mathlib


theorem algebra_325616 {a : ℝ} (ha : a ≠ 0) (h : a - 5 / a + 4 * Real.sqrt (a * (a - 3)) / a = 3) :
    ⌊a⌋ = -1 ∨ ⌊a⌋ = 3 := by

  have h1 : a ^ 2 - 3 * a - 5 + 4 * Real.sqrt (a * (a - 3)) = 0 := by
    have h2 : a ≠ 0 := ha
    have eq1 : a - 5 / a + 4 * Real.sqrt (a * (a - 3)) / a = 3 := by
      linarith
    field_simp at eq1 ⊢
    nlinarith

  have h4 : a * (a - 3) ≥ 0 := by
    by_contra h4
    push_neg at h4
    have h5 : Real.sqrt (a * (a - 3)) = 0 := by
      rw [Real.sqrt_eq_zero']
      nlinarith
    rw [h5] at h1
    nlinarith [sq_nonneg (a - 3 / 2)]

  have h3 : Real.sqrt (a * (a - 3)) ^ 2 = a * (a - 3) := by
    rw [Real.sq_sqrt]
    nlinarith

  have h5 : Real.sqrt (a * (a - 3)) = 1 := by
    have h8 : Real.sqrt (a * (a - 3)) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h9 : (Real.sqrt (a * (a - 3))) ^ 2 + 4 * Real.sqrt (a * (a - 3)) - 5 = 0 := by
      nlinarith [h1, h3]
    have h10 : Real.sqrt (a * (a - 3)) = 1 := by
      have h11 : (Real.sqrt (a * (a - 3))) ^ 2 + 4 * Real.sqrt (a * (a - 3)) - 5 = 0 := h9
      have h12 : (Real.sqrt (a * (a - 3)) + 5) * (Real.sqrt (a * (a - 3)) - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h12) with h13 h14
      · -- Real.sqrt (a * (a - 3)) + 5 = 0
        nlinarith [Real.sqrt_nonneg (a * (a - 3))]
      · -- Real.sqrt (a * (a - 3)) - 1 = 0
        linarith
    exact h10

  have h6 : a * (a - 3) = 1 := by
    calc
      a * (a - 3) = Real.sqrt (a * (a - 3)) ^ 2 := by rw [h3]
      _ = (1 : ℝ) ^ 2 := by rw [show Real.sqrt (a * (a - 3)) = 1 by linarith [h5]]
      _ = (1 : ℝ) := by norm_num

  have h7 : a ^ 2 - 3 * a - 1 = 0 := by
    nlinarith

  have h8 : (a - (3 + Real.sqrt 13) / 2) * (a - (3 - Real.sqrt 13) / 2) = 0 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (13 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]

  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case $a = \frac{3 + \sqrt{13}}{2}$
    have ha1 : a = (3 + Real.sqrt 13) / 2 := by linarith
    have h10 : ⌊a⌋ = 3 := by
      rw [ha1]
      have h11 : (3 : ℝ) < Real.sqrt 13 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (13 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      have h12 : Real.sqrt 13 < (4 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      have h13 : (3 : ℝ) < (3 + Real.sqrt 13) / 2 := by
        nlinarith
      have h14 : (3 + Real.sqrt 13) / 2 < (4 : ℝ) := by
        nlinarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith
    right
    exact h10
  · -- Case $a = \frac{3 - \sqrt{13}}{2}$
    have ha2 : a = (3 - Real.sqrt 13) / 2 := by linarith
    have h11 : ⌊a⌋ = -1 := by
      rw [ha2]
      have h14 : Real.sqrt 13 > (3 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (13 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      have h15 : Real.sqrt 13 < (4 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      have h17 : (3 - Real.sqrt 13) / 2 ≥ (-1 : ℝ) := by
        nlinarith
      have h18 : (3 - Real.sqrt 13) / 2 < (0 : ℝ) := by
        nlinarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith
    left
    exact h11