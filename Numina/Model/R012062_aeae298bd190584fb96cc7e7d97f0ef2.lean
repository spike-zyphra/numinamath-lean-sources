import Mathlib

theorem algebra_172638 (x y : ℝ) (a b : ℝ) (ha : a = 2 * x ^ 2 - y ^ 2 + 3 / 2) (hb : b = y ^ 4 + 4 * x + 2):
    a ≤ 1 ∧ b ≤ 1 ↔
    (x = -1 / 2 ∧ y = 1) ∨ (x = -1 / 2 ∧ y = -1) := by 
  constructor
  · -- Forward implication: assuming a ≤ 1 and b ≤ 1, proving the disjunction of the two conditions
    intro h
    rcases h with ⟨ha1, hb1⟩
    have h1: 2 * x ^ 2 - y ^ 2 ≤ -1 / 2 := by 
      nlinarith [ha, ha1]
    have h2: y ^ 4 + 4 * x ≤ -1 := by 
      nlinarith [hb, hb1]
    have h3 : (y - 1) * (y + 1) = 0 := by
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y ^ 2 - 1), sq_nonneg (y ^ 2 - 2 * x ^ 2 - 1 / 2)]
    have hy1 : y = 1 ∨ y = -1 := by 
      cases (mul_eq_zero.mp h3) with 
      | inl h4 => left; linarith 
      | inr h5 => right; linarith 
    cases hy1 with 
    | inl hy1 =>
      have h4 : x = -1 / 2 := by
        rw [hy1] at h2 
        nlinarith [h1, sq_nonneg (x + 1 / 2)]
      left 
      constructor 
      · -- x = -1/2 
        linarith [h4] 
      · -- y = 1 
        linarith [hy1] 
    | inr hy1 =>
      have h5 : x = -1 / 2 := by 
        rw [hy1] at h2 
        nlinarith [h1, sq_nonneg (x + 1 / 2)]
      right 
      constructor 
      · -- x = -1/2 
        linarith [h5] 
      · -- y = -1 
        linarith [hy1] 
  · -- Backward implication: proving that given either disjunction, both a and b satisfy the inequalities 
    rintro (h | h)
    · -- First solution 
      rcases h with ⟨hx1, hy1⟩ 
      constructor 
      · -- Compute and verify a ≤ 1 
        rw [ha] 
        rw [hx1, hy1] 
        norm_num 
      · -- Compute and verify b ≤ 1 
        rw [hb] 
        rw [hx1, hy1] 
        norm_num 
    · -- Second solution 
      rcases h with ⟨hx1, hy2⟩ 
      constructor 
      · -- Compute and verify a ≤ 1 
        rw [ha] 
        rw [hx1, hy2] 
        norm_num 
      · -- Compute and verify b ≤ 1 
        rw [hb] 
        rw [hx1, hy2] 
        norm_num