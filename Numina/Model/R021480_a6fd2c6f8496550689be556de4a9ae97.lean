import Mathlib

theorem algebra_130406 {a : ℝ} (ha : a ≠ -4) :
    (∃ x, 3 * x ^ 2 - x - a - 10 = 0 ∧ (a + 4) * x + a + 12 = 0) ↔
    a = -10 ∨ a = -8 ∨ a = 4 := by 
  constructor
  · -- Forward direction: If such an x exists, then a ∈ {-10, -8, 4}
    rintro ⟨x, h1, h2⟩
    have h3 : a + 4 ≠ 0 := by
      intro h'
      apply ha
      linarith
    have hx2 : x = (-a - 12) / (a + 4) := by
      have h14 : a + 4 ≠ 0 := h3
      field_simp [h14] at *
      nlinarith
      all_goals nlinarith
    rw [hx2] at h1
    have h7 : 3 * (-a - 12) ^ 2 - (-a - 12) * (a + 4) - (a + 10) * (a + 4) ^ 2 = 0 := by
      have h8' : 3 * ((-a - 12) / (a + 4)) ^ 2 - ((-a - 12) / (a + 4)) - a - 10 = 0 := by
        linarith [h1]
      have h8 : a + 4 ≠ 0 := h3
      have h9 : 3 * ((-a - 12) / (a + 4)) ^ 2 - ((-a - 12) / (a + 4)) - a - 10 = 0 := by
        linarith [h1]
      have h10 : 3 * (-a - 12) ^ 2 - (-a - 12) * (a + 4) - (a + 10) * (a + 4) ^ 2 = 0 := by
        have h8 : a + 4 ≠ 0 := h3
        have eq1 : 3 * ((-a - 12) / (a + 4)) ^ 2 - ((-a - 12) / (a + 4)) - a - 10 =
            (3 * (-a - 12) ^ 2 - (-a - 12) * (a + 4) - (a + 10) * (a + 4) ^ 2) / ((a + 4) ^ 2) := by
          field_simp [h8]
          <;> ring
        rw [eq1] at h9
        have h11 : (3 * (-a - 12) ^ 2 - (-a - 12) * (a + 4) - (a + 10) * (a + 4) ^ 2) / ((a + 4) ^ 2) = 0 := by
          linarith
        have h12 : (3 * (-a - 12) ^ 2 - (-a - 12) * (a + 4) - (a + 10) * (a + 4) ^ 2) = 0 := by
          have h14 : (a + 4) ^ 2 ≠ 0 := by
            apply pow_ne_zero 2
            exact h8
          field_simp [h14] at h11 ⊢
          <;> nlinarith
          all_goals nlinarith
        linarith
      linarith
    have h3' : (a + 10) * (a + 8) * (a - 4) = 0 := by
      nlinarith [sq_nonneg (a + 4), sq_nonneg (a + 8), sq_nonneg (a - 4), sq_nonneg (a + 10), sq_pos_of_ne_zero (show a + 4 ≠ 0 by assumption)]
    cases' (mul_eq_zero.mp h3') with h4 h5
    · cases' (mul_eq_zero.mp h4) with h6 h7
      · -- a + 10 = 0
        left
        linarith
      · -- a + 8 = 0
        right
        left
        linarith
    · -- a - 4 = 0
      right
      right
      linarith
  · -- Backward direction: For each a ∈ {-10, -8, 4}, there exists such an x
    rintro (h | h | h)
    · -- a = -10
      rw [h]
      use 1 / 3
      constructor
      · -- First equation
        norm_num
      · -- Second equation
        norm_num
    · -- a = -8
      rw [h]
      use 1
      constructor
      · -- First equation
        norm_num
      · -- Second equation
        norm_num
    · -- a = 4
      rw [h]
      use -2
      constructor
      · -- First equation
        norm_num
      · -- Second equation
        norm_num