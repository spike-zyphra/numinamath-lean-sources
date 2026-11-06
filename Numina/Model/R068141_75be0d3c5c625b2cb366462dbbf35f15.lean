import Mathlib

theorem algebra_118674 (q : ℝ) :
    (∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1^2 - 12 * x1 + q = 0 ∧ x2^2 - 12 * x2 + q = 0 ∧ x1 = x2^2) ↔
    q = -64 ∨ q = 27 := by
  constructor
  · -- Assume the existence of the two distinct roots with the given property, prove q ∈ { -64, 27 }
    intro h
    rcases h with ⟨x1, x2, hneq, eq1, eq2, eq3⟩
    have eq4 : q = 12 * x2 - x2 ^ 2 := by linarith [eq2]
    rw [eq3] at eq1
    have h' : x2 * (x2 ^ 3 - 13 * x2 + 12) = 0 := by
      nlinarith [eq1, eq2, hneq]
    cases' (mul_eq_zero.mp h') with hx2 hx3
    · -- Case x2 = 0
      have hq : q = 0 := by
        nlinarith [eq4, hx2]
      have h1 : x1 = 0 := by
        rw [show x2 = (0 : ℝ) by linarith [hx2]] at eq3
        nlinarith
      have h2 : x2 = 0 := by
        linarith [hx2]
      exfalso
      exact hneq (by linarith [h1, h2])
    · -- Case x2 ^ 3 - 13 * x2 + 12 = 0
      have h_cubic : x2 ^ 3 - 13 * x2 + 12 = 0 := by
        linarith [hx3]
      have factored : (x2 - 1) * ((x2 - 3) * (x2 + 4)) = 0 := by
        nlinarith [h_cubic, sq_nonneg (x2 ^ 2), sq_nonneg (x2 - 1), sq_nonneg (x2 - 3), sq_nonneg (x2 + 4)]
      cases' (mul_eq_zero.mp factored) with h1 h2
      · -- Case (x2 - 1) = 0
        have hx2_eq_1 : x2 = 1 := by linarith [h1]
        have hq : q = 11 := by
          rw [show x2 = (1 : ℝ) by linarith [hx2_eq_1]] at eq4
          linarith [eq4]
        have h1' : x1 = 1 := by
          rw [show x2 = (1 : ℝ) by linarith [hx2_eq_1]] at eq3
          nlinarith
        have h2 : x2 = 1 := by linarith [hx2_eq_1]
        exfalso
        exact hneq (by linarith [h1', h2])
      · -- Case (x2 - 3) * (x2 + 4) = 0
        have h_zero_sub_cases : (x2 - 3) * (x2 + 4) = 0 := by
          nlinarith [h2]
        cases' (mul_eq_zero.mp h_zero_sub_cases) with h3 h4
        · -- Case x2 - 3 = 0, so x2 = 3
          have hx2_eq_3 : x2 = 3 := by linarith [h3]
          have hq_eq_27 : q = 27 := by
            rw [show x2 = (3 : ℝ) by linarith [hx2_eq_3]] at eq4
            linarith
          right
          exact_mod_cast hq_eq_27
        · -- Case x2 + 4 = 0, so x2 = -4
          have hx2_eq_neg4 : x2 = -4 := by linarith [h4]
          have hq_eq_neg64 : q = -64 := by
            rw [show x2 = (-4 : ℝ) by linarith [hx2_eq_neg4]] at eq4
            linarith
          left
          exact_mod_cast hq_eq_neg64
  · -- Assume q ∈ { -64, 27 }, prove the existence of the two distinct roots with the given property
    rintro (hq | hq)
    · -- Case q = -64
      rw [hq]
      use 16, -4
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Case q = 27
      rw [hq]
      use 9, 3
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num