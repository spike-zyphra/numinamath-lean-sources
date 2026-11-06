import Mathlib

open Real Set

theorem algebra_13384 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a^2 + b^2 + 1 / a^2 + b / a ≥ sqrt 3 ∧
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a^2 + b^2 + 1 / a^2 + b / a = sqrt 3 := by
  have h1 : b^2 + b / a = (b + 1 / (2 * a))^2 - 1 / (4 * a^2) := by
    field_simp
    ring
  have h2 : a^2 + b^2 + 1 / a^2 + b / a = a^2 + 3 / (4 * a^2) + (b + 1 / (2 * a))^2 := by
    field_simp
    nlinarith [sq_nonneg (b + 1 / (2 * a)), sq_nonneg (a ^ 2 - Real.sqrt 3 / 2), Real.sqrt_nonneg 3]
  have h3 : a^2 + 3 / (4 * a^2) ≥ Real.sqrt 3 := by
    have h4 : a^2 > 0 := by
      exact sq_pos_of_ne_zero (show a ≠ 0 by assumption)
    have h5 : a^2 + 3 / (4 * a^2) - Real.sqrt 3 ≥ 0 := by
      have h6 : a ^ 2 + 3 / (4 * a ^ 2) - Real.sqrt 3 =
          ( (a ^ 2) ^ 2 - Real.sqrt 3 * (a ^ 2) + 3 / 4 ) / (a ^ 2) := by
        field_simp
        ring
      rw [h6]
      apply div_nonneg
      have h7 : (a ^ 2) ^ 2 - Real.sqrt 3 * (a ^ 2) + 3 / 4 ≥ 0 := by
        nlinarith [sq_nonneg ( (a ^ 2) - Real.sqrt 3 / 2 ), Real.sqrt_nonneg 3,
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
        ]
      linarith
      positivity
    linarith
  constructor
  · -- First part of the conjunction: prove the inequality
    nlinarith [Real.sqrt_nonneg 3, sq_nonneg (b + 1 / (2 * a)), sq_nonneg (a ^ 2 - Real.sqrt 3 / 2), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), h2, h3]
  · -- Second part of the conjunction: prove the existence.
    have h7 : ∃a : ℝ, a ≠ 0 ∧ a^4 = 3 / 4 := by
      use Real.sqrt (Real.sqrt (3 / 4))
      constructor
      · -- Show `a ≠ 0`:
        by_contra h
        have h8 : Real.sqrt (Real.sqrt (3 / 4)) = 0 := by
          linarith [h]
        have h9 : Real.sqrt (3 / 4) > 0 := by
          apply Real.sqrt_pos.mpr
          norm_num
        have h10 : Real.sqrt (Real.sqrt (3 / 4)) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith [h9]
        linarith [h8, h10]
      · -- Show `a^4 = 3 / 4`:
        have h10 : (Real.sqrt (Real.sqrt (3 / 4)) ^ 2) ^ 2 = 3 / 4 := by
          calc
            (Real.sqrt (Real.sqrt (3 / 4)) ^ 2) ^ 2
              = (Real.sqrt (3 / 4)) ^ 2 := by
                rw [Real.sq_sqrt]
                positivity
            _ = 3 / 4 := by
                rw [Real.sq_sqrt]
                positivity
        nlinarith [h10]
    rcases h7 with ⟨a, ha1, ha2⟩
    use a
    use -1 / (2 * a)
    constructor
    · -- Show a ≠ 0
      exact ha1
    constructor
    · -- Show b ≠ 0
      by_contra h
      have h10 : -1 / (2 * a) = 0 := by
        linarith [h]
      have h11 : -1 / (2 * a) = 0 := by
        linarith [h10]
      field_simp [ha1] at h11
    · -- Show the expression is sqrt 3
      have ha3 : a^2 > 0 := by
        nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption), Real.sqrt_nonneg 3]
      have h8 : a ^ 2 + (-1 / (2 * a))^2 + 1 / a ^ 2 + (-1 / (2 * a)) / a = a^2 + 3 / (4 * a^2) := by
        field_simp
        ring
      rw [h8]
      have h9 : a ^ 2 + 3 / (4 * a ^ 2) = Real.sqrt 3 := by
        have h10 : (a ^ 2)^2 = 3 / 4 := by
          nlinarith [ha2]
        have h11 : a ^ 2 = Real.sqrt 3 / 2 := by
          have h12 : (a ^ 2) ^ 2 = 3 / 4 := h10
          have h13 : a ^ 2 > 0 := ha3
          have h14 : a ^ 2 = Real.sqrt (3 / 4) := by
            have h15 : Real.sqrt ((a ^ 2) ^ 2) = a ^ 2 := by
              rw [Real.sqrt_sq]
              positivity
            have h16 : Real.sqrt ((a ^ 2) ^ 2) = Real.sqrt (3 / 4) := by
              rw [h12]
            linarith [h15, h16]
          have h17 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num <;> ring_nf <;> norm_num
          rw [h17] at h14
          linarith
        rw [h11]
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      linarith [h9]