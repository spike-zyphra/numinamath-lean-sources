import Mathlib

theorem algebra_234843 (a : ℝ) :
    (∃ x : ℝ, a * x + a = x ∧ x = 2 - 2 * a * x) ↔ a = 1 / 2 ∨ a = -2 := by
  constructor
  · -- Forward direction: if there exists an x such that both equations hold, then a = 1/2 or a = -2
    rintro ⟨x, ⟨h1, h2⟩⟩
    have eq1 : x * (1 - a) = a := by
      nlinarith 
    have eq2 : x * (1 + 2 * a) = 2 := by
      nlinarith 
    by_cases h : 1 - a = 0
    · -- Case where 1 - a = 0, which means a = 1
      have ha : a = 1 := by linarith 
      rw [ha] at eq1 
      nlinarith
    · -- Case where 1 - a ≠ 0
      have hx1 : x = a / (1 - a) := by
        field_simp [show (1 - a) ≠ 0 by intro h1; apply h; linarith]
        linarith
      have hx2 : x = 2 / (1 + 2 * a) := by
        have h2a : 1 + 2 * a ≠ 0 := by
          by_contra h2
          have : 1 + 2 * a = 0 := by linarith
          have : x * (1 + 2 * a) = 0 := by
            rw [this]
            ring
          linarith
        field_simp [h2a]
        nlinarith
      have h_eq : a / (1 - a) = 2 / (1 + 2 * a) := by 
        rw [hx1] at *
        rw [hx2] at *
        all_goals linarith
      have h_eq2 : a * (1 + 2 * a) = 2 * (1 - a) := by
        have h1 : 1 - a ≠ 0 := by 
          intro h1
          apply h
          linarith
        have h2 : 1 + 2 * a ≠ 0 := by 
          by_contra h2
          have : 1 + 2 * a = 0 := by linarith
          have : x * (1 + 2 * a) = 0 := by
            rw [this]
            ring
          linarith
        field_simp [h1, h2] at h_eq 
        nlinarith 
      have h_eq4 : 2 * a^2 + 3 * a - 2 = 0 := by
        nlinarith 
      have h_eq5 : (a - 1 / 2) * (2 * a + 4) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp h_eq5) with h6 h7
      · -- Case where a - 1/2 = 0, so a = 1/2
        left 
        linarith 
      · -- Case where 2a + 4 = 0, so a = -2
        right 
        linarith 
  · -- Backward direction: if a = 1/2 or a = -2, then there exists x
    rintro (ha | ha)
    · -- Case a = 1/2
      use 1
      rw [ha]
      constructor
      · norm_num 
      · norm_num 
    · -- Case a = -2
      use -2 / 3
      rw [ha]
      constructor
      · norm_num 
      · norm_num