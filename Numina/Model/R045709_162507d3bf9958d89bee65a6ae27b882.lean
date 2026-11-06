import Mathlib

theorem algebra_310210 (a b c : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 1 ≤ b ∧ b ≤ 9) (hc : 1 ≤ c ∧ c ≤ 9)
    (h : (1 / a : ℚ) * (1 - 1 / b : ℚ) * (1 - 1 / c : ℚ) +
      (1 - 1 / a : ℚ) * (1 / b : ℚ) * (1 - 1 / c : ℚ) +
      (1 - 1 / a : ℚ) * (1 - 1 / b : ℚ) * (1 / c : ℚ) = 7 / 15) :
    (1 - 1 / a : ℚ) * (1 - 1 / b : ℚ) * (1 - 1 / c : ℚ) = 4 / 15 := by 
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at h ⊢ <;> all_goals
  omega