import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_188517 :
  IsLeast {x | ∃ a b : ℝ, x = a^3 + b^3 ∧ 3^(-a) * b^4 - 2 * b^2 + 3^a ≤ 0 ∧ 27^a + b^4 - 3^a - 1 = 0} (-1) := by
  constructor
  · -- We need to prove -1 ∈ the set
    use 0, -1
    norm_num
  · -- We need to prove for all x ∈ the set, -1 ≤ x
    rintro x ⟨a, b, hx, h1, h2⟩
    have h3 : (3 : ℝ) ^ a > 0 := by positivity
    have h4 : (3 : ℝ) ^ (-a : ℝ) > 0 := by positivity
    have h5 : (3 : ℝ) ^ (-a : ℝ) = 1 / (3 : ℝ) ^ a := by
      field_simp [Real.rpow_neg]
    have h6 : (b^2 - (3 : ℝ) ^ a)^2 ≤ 0 := by
      have h7 : ((3 : ℝ) ^ (-a : ℝ)) * (b^4) - 2 * (b^2) + (3 : ℝ) ^ a ≤ 0 := by linarith
      rw [h5] at h7
      have h8 : (b^4 - 2 * (3 : ℝ) ^ a * (b^2) + ((3 : ℝ) ^ a)^2) ≤ 0 := by
        have h9 : (3 : ℝ) ^ a > 0 := by positivity
        have h10 : (b^4 - 2 * (3 : ℝ) ^ a * (b^2) + ((3 : ℝ) ^ a)^2) = ((3 : ℝ) ^ a) * ((b^4 / (3 : ℝ) ^ a) - 2 * (b^2) + (3 : ℝ) ^ a) := by
          field_simp [h9]
          <;> ring
        rw [h10]
        have h11 : (b^4 / (3 : ℝ) ^ a) - 2 * (b^2) + (3 : ℝ) ^ a ≤ 0 := by
          have h12 : (b^4 / (3 : ℝ) ^ a) - 2 * (b^2) + (3 : ℝ) ^ a = ((3 : ℝ) ^ (-a : ℝ)) * (b^4) - 2 * (b^2) + (3 : ℝ) ^ a := by
            rw [h5]
            field_simp [h3]
            all_goals linarith
          linarith [h12, h7]
        nlinarith [h11, h3]
      nlinarith [sq_nonneg (b^2 - (3 : ℝ) ^ a)]
    have h8 : (b^2 - (3 : ℝ) ^ a)^2 = 0 := by
      nlinarith [sq_nonneg (b^2 - (3 : ℝ) ^ a)]
    have h9 : b^2 - (3 : ℝ) ^ a = 0 := by
      rw [sq_eq_zero_iff] at h8
      exact h8
    have h10 : (3 : ℝ) ^ a = b^2 := by linarith [h9]
    have h11 : (27 : ℝ) ^ a = (3 : ℝ) ^ (3 * a) := by
      rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h12 : (3 : ℝ) ^ (3 * a) = ((3 : ℝ) ^ a)^3 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h11, h12, h10] at h2
    have h13 : b^6 + b^4 - b^2 - 1 = 0 := by
      nlinarith
    have h14 : (b^2 - 1) * (b^2 + 1)^2 = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h14) with h15 h16
    · -- Case where b^2 - 1 = 0 implies b^2 = 1
      have h17 : b^2 = 1 := by linarith
      have h18 : (3 : ℝ) ^ a = 1 := by
        nlinarith [h10, h17]
      have ha : a = 0 := by
        apply_fun (Real.logb (3 : ℝ)) at h18
        simp at h18 ⊢
        exact h18
      have hb : b = 1 ∨ b = -1 := by
        have h19 : b^2 = 1 := h17
        rw [sq_eq_one_iff] at h19
        exact h19
      rcases hb with hb | hb
      · -- Case where b = 1
        rw [hx, ha, hb]
        norm_num
      · -- Case where b = -1
        rw [hx, ha, hb]
        norm_num
    · -- Case where (b^2 + 1)^2 = 0
      have h18 : (b^2 + 1)^2 = 0 := by
        nlinarith
      have h19 : b^2 + 1 = 0 := by
        nlinarith [sq_nonneg (b^2 + 1), h18]
      nlinarith [sq_nonneg b, h19]