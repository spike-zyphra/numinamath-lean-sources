import Mathlib

theorem algebra_12695 : IsGreatest {x : ℝ | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
    a + b + c = 1 ∧ x = a * b / (a + b) + a * c / (a + c) + b * c / (b + c)} (1 / 2) := by
  constructor
  · -- First, show that 1/2 is in the set
    use 1 / 3, 1 / 3, 1 / 3
    norm_num
  · -- Now, show that 1/2 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : a * b / (a + b) + a * c / (a + c) + b * c / (b + c) ≤ 1 / 2 := by
      have h11 : a * b / (a + b) ≤ (a + b) / 4 := by
        by_cases h2 : a + b = 0 
        · -- If a + b = 0, then a = b = 0 
          have ha0 : a = 0 := by linarith [show a ≥ 0 from ha, show b ≥ 0 from hb, h2]
          have hb0 : b = 0 := by linarith [show a ≥ 0 from ha, show b ≥ 0 from hb, h2]
          rw [ha0, hb0]
          norm_num 
        have h3 : a + b > 0 := by 
          by_contra h 
          push_neg at h 
          have : a + b = 0 := by linarith 
          contradiction 
        have h5 : a * b / (a + b) ≤ (a + b) / 4 := by 
          have h12 : a * b ≤ ((a + b) ^ 2) / 4 := by 
            nlinarith [sq_nonneg (a - b)]
          have h13 : a * b / (a + b) ≤ ((a + b) ^ 2 / 4) / (a + b) := by 
            apply (div_le_div_right h3).mpr 
            nlinarith 
          have h14 : ((a + b) ^ 2 / 4) / (a + b) = (a + b) / 4 := by 
            field_simp 
            <;> nlinarith 
          linarith 
        exact h5
      have h12 : a * c / (a + c) ≤ (a + c) / 4 := by
        by_cases h2 : a + c = 0 
        · -- If a + c = 0, then a = c = 0 
          have ha0 : a = 0 := by linarith [show a ≥ 0 from ha, show c ≥ 0 from hc, h2]
          have hc0 : c = 0 := by linarith [show a ≥ 0 from ha, show c ≥ 0 from hc, h2]
          rw [ha0, hc0]
          norm_num 
        have h3 : a + c > 0 := by 
          by_contra h 
          push_neg at h 
          have : a + c = 0 := by linarith 
          contradiction 
        have h5 : a * c / (a + c) ≤ (a + c) / 4 := by 
          have h12 : a * c ≤ ((a + c) ^ 2) / 4 := by 
            nlinarith [sq_nonneg (a - c)]
          have h13 : a * c / (a + c) ≤ ((a + c) ^ 2 / 4) / (a + c) := by 
            apply (div_le_div_right h3).mpr 
            nlinarith 
          have h14 : ((a + c) ^ 2 / 4) / (a + c) = (a + c) / 4 := by 
            field_simp 
            <;> nlinarith 
          linarith 
        exact h5
      have h13 : b * c / (b + c) ≤ (b + c) / 4 := by
        by_cases h2 : b + c = 0 
        · -- If b + c = 0, then b = c = 0 
          have hb0 : b = 0 := by linarith [show b ≥ 0 from hb, show c ≥ 0 from hc, h2]
          have hc0 : c = 0 := by linarith [show b ≥ 0 from hb, show c ≥ 0 from hc, h2]
          rw [hb0, hc0]
          norm_num 
        have h3 : b + c > 0 := by 
          by_contra h 
          push_neg at h 
          have : b + c = 0 := by linarith 
          contradiction 
        have h5 : b * c / (b + c) ≤ (b + c) / 4 := by 
          have h12 : b * c ≤ ((b + c) ^ 2) / 4 := by 
            nlinarith [sq_nonneg (b - c)]
          have h13 : b * c / (b + c) ≤ ((b + c) ^ 2 / 4) / (b + c) := by 
            apply (div_le_div_right h3).mpr 
            nlinarith 
          have h14 : ((b + c) ^ 2 / 4) / (b + c) = (b + c) / 4 := by 
            field_simp 
            <;> nlinarith 
          linarith 
        exact h5
      have h14 : a * b / (a + b) + a * c / (a + c) + b * c / (b + c) ≤ 1 / 2 := by
        linarith [h11, h12, h13, show (a + b) / 4 + (a + c) / 4 + (b + c) / 4 = 1 / 2 by
          nlinarith
        ]
      linarith 
    linarith [hx, h2]