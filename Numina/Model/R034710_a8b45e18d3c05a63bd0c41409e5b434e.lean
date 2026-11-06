import Mathlib

theorem algebra_187340 (x : ℝ) : (5 : ℝ)^(2 * x) - 7 * (5 : ℝ)^x + 10 = 0 ↔ x = 1 ∨ x = Real.logb 5 2 := by
  constructor
  · -- Assume (5 : ℝ)^(2 * x) - 7 * (5 : ℝ)^x + 10 = 0, prove x = 1 ∨ x = Real.logb 5 2
    intro h
    have h1 : (5 : ℝ) ^ (2 * x) = ((5 : ℝ) ^ x) ^ 2 := by
      calc
        (5 : ℝ) ^ (2 * x) = (5 : ℝ) ^ (x + x) := by ring_nf
        _ = (5 : ℝ) ^ x * (5 : ℝ) ^ x := by rw [← Real.rpow_add]; ring_nf; all_goals linarith
        _ = ((5 : ℝ) ^ x) ^ 2 := by ring
    rw [h1] at h
    have h2 : ((5 : ℝ) ^ x) ^ 2 - 7 * ((5 : ℝ) ^ x) + 10 = 0 := by
      linarith
    have h3 : ((5 : ℝ) ^ x - 2) * ((5 : ℝ) ^ x - 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- $5^x - 2 = 0$
      have h6 : (5 : ℝ) ^ x = (2 : ℝ) := by
        linarith
      have h7 : x = Real.logb (5 : ℝ) (2 : ℝ) := by
        rw [← h6]
        field_simp
      right
      rw [h7]
      all_goals norm_num
    · -- $5^x - 5 = 0$
      have h8 : (5 : ℝ) ^ x = (5 : ℝ) := by
        linarith
      have h9 : x = (1 : ℝ) := by
        apply_fun (Real.logb (5 : ℝ)) at h8
        have h10 : Real.logb (5 : ℝ) ((5 : ℝ) ^ x) = x := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h11 : Real.logb (5 : ℝ) (5 : ℝ) = (1 : ℝ) := by
          norm_num [Real.logb_eq_iff_rpow_eq]
        rw [h10] at h8
        rw [h11] at h8
        linarith
      left
      linarith
  · -- Assume x = 1 ∨ x = Real.logb 5 2, prove (5 : ℝ)^(2 * x) - 7 * (5 : ℝ)^x + 10 = 0
    rintro (h | h)
    · -- x = 1
      rw [h]
      norm_num
    · -- x = Real.logb 5 2
      rw [h]
      have h1 : (5 : ℝ) ^ (2 * (Real.logb (5 : ℝ) (2 : ℝ))) = ((5 : ℝ) ^ (Real.logb (5 : ℝ) (2 : ℝ))) ^ 2 := by
        calc
          (5 : ℝ) ^ (2 * (Real.logb (5 : ℝ) (2 : ℝ))) = (5 : ℝ) ^ (Real.logb (5 : ℝ) (2 : ℝ) + Real.logb (5 : ℝ) (2 : ℝ)) := by ring_nf
          _ = (5 : ℝ) ^ (Real.logb (5 : ℝ) (2 : ℝ)) * (5 : ℝ) ^ (Real.logb (5 : ℝ) (2 : ℝ)) := by rw [← Real.rpow_add]; ring_nf; all_goals linarith
          _ = ((5 : ℝ) ^ (Real.logb (5 : ℝ) (2 : ℝ))) ^ 2 := by ring
      have h2 : (5 : ℝ) ^ (Real.logb (5 : ℝ) (2 : ℝ)) = (2 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals norm_num
      rw [h1, h2]
      norm_num