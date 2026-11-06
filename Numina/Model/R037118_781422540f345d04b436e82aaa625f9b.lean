import Mathlib

theorem algebra_218360 (a : ℝ) :
    (∃ x y, x + y = 0 ∧ x^3 - a * y^3 = (1 / 2) * (a + 1)^2 ∧
      x^3 + a * x^2 * y + x * y^2 = 1) ↔ (a = 0 ∨ a = -1 ∨ a = 1) := by
  constructor
  · -- Assume there exists a solution with x + y = 0, prove a = 0 ∨ a = -1 ∨ a = 1
    rintro ⟨x, y, hxy, h1, h2⟩
    have hy : y = -x := by linarith
    rw [hy] at h1 h2
    have eq1 : x^3 * (1 + a) = (1 / 2) * (a + 1)^2 := by
      have h1' : x^3 - a * (-x) ^ 3 = (1 / 2) * (a + 1)^2 := by linarith [h1]
      have eq2 : x^3 - a * (-x) ^ 3 = x^3 * (1 + a) := by
        ring_nf
      linarith [h1', eq2]
    -- Second equation simplifies to x^3 * (2 - a) = 1
    have eq2 : x^3 * (2 - a) = 1 := by
      have h2' : x^3 + a * x^2 * (-x) + x * (-x) ^ 2 = 1 := by linarith [h2]
      have eq3 : x^3 + a * x^2 * (-x) + x * (-x) ^ 2 = x^3 * (2 - a) := by
        ring_nf
      linarith [h2', eq3]
    by_cases h3 : 2 - a = 0
    · -- If 2 - a = 0, then a = 2
      have ha : a = 2 := by linarith
      rw [ha] at eq2
      norm_num at eq2
      all_goals linarith
    · -- Case 2 - a ≠ 0
      have eq3 : x^3 = 1 / (2 - a) := by
        have h4 : 2 - a ≠ 0 := by
          by_contra h
          have h2 : a = 2 := by linarith
          contradiction
        field_simp [h4]
        linarith [eq2]
      rw [eq3] at eq1
      have eq5 : 2 * (1 + a) = (a + 1) ^ 2 * (2 - a) := by
        have h4' : (2 - a : ℝ) ≠ 0 := by
          by_contra h
          have h2 : a = 2 := by linarith
          contradiction
        field_simp [h4'] at eq1
        nlinarith
      have eq6 : a^3 - a = 0 := by
        nlinarith
      have eq7 : a * (a^2 - 1) = 0 := by
        linarith [eq6]
      cases' (mul_eq_zero.mp eq7) with h8 h9
      · -- Case a = 0
        left
        linarith
      · -- Case a^2 - 1 = 0
        have h10 : a^2 = 1 := by
          linarith [h9]
        have h11 : a = 1 ∨ a = -1 := by
          rw [sq_eq_one_iff] at h10
          tauto
        cases' h11 with h12 h13
        · -- Case a = 1
          right
          right
          linarith
        · -- Case a = -1
          right
          left
          linarith
  · -- Assume a = 0 ∨ a = -1 ∨ a = 1 prove there exists a solution
    rintro (h | h | h)
    · -- Case a = 0
      have ha0 : a = 0 := by linarith
      use (1 / 2) ^ (1 / 3 : ℝ)
      use - (1 / 2) ^ (1 / 3 : ℝ)
      constructor
      · -- Show that x + y = 0
        ring_nf
      constructor
      · -- Show that x^3 - a * y^3 = (1 / 2) * (a + 1)^2
        rw [ha0]
        have h14 : ((1 / 2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        nlinarith [h14]
      · -- Show that x^3 + a * x^2 * y + x * y^2 = 1
        rw [ha0]
        have h14 : ((1 / 2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        nlinarith [h14]
    · -- Case a = -1
      have ha1 : a = -1 := by linarith
      use (1 / 3) ^ (1 / 3 : ℝ)
      use - (1 / 3) ^ (1 / 3 : ℝ)
      constructor
      · -- Show that x + y = 0
        ring_nf
      constructor
      · -- Show that x^3 - a * y^3 = (1 / 2) * (a + 1)^2
        rw [ha1]
        have h14 : ((1 / 3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        nlinarith [h14]
      · -- Show that x^3 + a * x^2 * y + x * y^2 = 1
        rw [ha1]
        have h14 : ((1 / 3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        nlinarith [h14]
    · -- Case a = 1
      have ha1 : a = 1 := by linarith
      use 1
      use -1
      constructor
      · -- Show that x + y = 0
        norm_num
      constructor
      · -- Show that x^3 - a * y^3 = (1 / 2) * (a + 1)^2
        rw [ha1]
        norm_num
      · -- Show that x^3 + a * x^2 * y + x * y^2 = 1
        rw [ha1]
        norm_num