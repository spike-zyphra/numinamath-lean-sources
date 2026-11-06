import Mathlib

theorem algebra_234829 (x : ℝ) :
    (x - 2020)^2 + (x - 2020)^10 = 2 * (x - 2020)^12 ↔
    x = 2019 ∨ x = 2020 ∨ x = 2021 := by
  constructor
  · -- Assume (x - 2020)^2 + (x - 2020)^10 = 2 * (x - 2020)^12, prove x = 2019 ∨ x = 2020 ∨ x = 2021
    intro h
    have eq1 : (x - 2020)^2 * (2 * (x - 2020)^10 - (x - 2020)^8 - 1) = 0 := by
      nlinarith [sq_nonneg ((x - 2020)^2), sq_nonneg ((x - 2020)^4), sq_nonneg ((x - 2020)^6), sq_nonneg ((x - 2020)^8)]
    cases' (mul_eq_zero.mp eq1) with h2 h3
    · -- case where (x - 2020)^2 = 0
      have hx1 : x - 2020 = 0 := by
        apply pow_eq_zero 
        exact h2
      have hx2 : x = 2020 := by linarith
      right
      left
      exact hx2
    · -- case where 2 * (x - 2020)^10 - (x - 2020)^8 - 1 = 0 
      have eq2 : 2 * (x - 2020)^10 - (x - 2020)^8 - 1 = 0 := by
        linarith
      have eq3 : (x - 2020)^2 - 1 = 0 := by
        nlinarith [sq_nonneg ((x - 2020)^2 - 1), sq_nonneg ((x - 2020)^2 + 1), sq_nonneg ((x - 2020)^4), sq_nonneg ((x - 2020)^6), sq_nonneg ((x - 2020)^2), sq_nonneg ((x - 2020)^2 - (x - 2020)^8 / 2)]
      have eq4 : (x - 2020)^2 = 1 := by 
        nlinarith
      have h1 : x - 2020 = 1 ∨ x - 2020 = -1 := by 
        have h2 : (x - 2020) ^ 2 = 1 := eq4
        have : x - 2020 = 1 ∨ x - 2020 = -1 := by
          rw [sq_eq_one_iff] at h2
          tauto
        assumption
      cases' h1 with h1 h1
      · -- case x - 2020 = 1
        have hx2 : x = 2021 := by linarith
        right
        right
        exact hx2
      · -- case x - 2020 = -1
        have hx2 : x = 2019 := by linarith
        left
        exact hx2
  · -- Assume x = 2019 ∨ x = 2020 ∨ x = 2021, prove (x - 2020)^2 + (x - 2020)^10 = 2 * (x - 2020)^12
    rintro (h | h | h)
    · -- case x = 2019
      rw [h]
      norm_num
    · -- case x = 2020
      rw [h]
      norm_num
    · -- case x = 2021
      rw [h]
      norm_num