import Mathlib
open Real

theorem inequalities_114611 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    a + b + c ≥ sqrt 3 ∧
    (a + b + c = sqrt 3 ↔ a = b ∧ b = c ∧ c = sqrt 3 / 3) := by
  have h1 : (a + b + c) ^ 2 ≥ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h4 : a + b + c ≥ sqrt 3 := by
    have h5 : (a + b + c) ^ 2 ≥ 3 := h1
    have h6 : sqrt ((a + b + c) ^ 2) ≥ sqrt 3 := by
      apply Real.sqrt_le_sqrt
      linarith
    have h7 : sqrt ((a + b + c) ^ 2) = a + b + c := by
      rw [Real.sqrt_sq (by positivity)]
    linarith [h7, h6]
  have h_eq : a + b + c = sqrt 3 ↔ a = b ∧ b = c ∧ c = sqrt 3 / 3 := by
    constructor
    · -- Assume $a + b + c = \sqrt{3}$ to prove $a = b ∧ b = c ∧ c = \sqrt{3}/3$.
      intro h_eq
      have h5 : (a + b + c) ^ 2 = 3 := by
        calc
          (a + b + c) ^ 2 = (sqrt 3) ^ 2 := by rw [h_eq]
          _ = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      have h5' : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
        nlinarith
      have h6 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have h7 : (a - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have h8 : a = b := by
        nlinarith
      have h9 : a = c := by
        nlinarith
      have h10 : b = c := by
        nlinarith
      have h11 : c = sqrt 3 / 3 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      constructor
      · exact_mod_cast h8
      constructor
      · exact_mod_cast h10
      · exact_mod_cast h11
    · -- Assume $a = b ∧ b = c ∧ c = \sqrt{3}/3$ to prove $a + b + c = \sqrt{3}$.
      rintro ⟨ha1, hb1, hc1⟩
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  exact ⟨h4, h_eq⟩