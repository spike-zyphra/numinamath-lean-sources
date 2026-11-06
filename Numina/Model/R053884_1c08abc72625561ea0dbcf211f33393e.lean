import Mathlib

theorem algebra_246159 {x y : ℕ} (h₀ : x + y = 830) (h₁ : max x y / min x y = 22) (h₂ : max x y % min x y = 2) :
    max x y = 794 := by
  by_cases h4 : x ≥ y
  · -- If x ≥ y, then max x y = x and min x y = y
    have h5 : max x y = x := by
      rw [max_eq_left h4]
    have h6 : min x y = y := by
      rw [min_eq_right h4]
    rw [h5, h6] at h₁ h₂
    have h7 : x = 22 * y + 2 := by
      rw [←Nat.div_add_mod x y, h₁, h₂]
      all_goals omega
    rw [h7] at h₀
    have h8 : y = 36 := by
      omega
    have h9 : x = 794 := by
      calc
        x = 22 * y + 2 := h7
        _ = 22 * 36 + 2 := by rw [h8]
        _ = 794 := by norm_num
    have h10 : max x y = 794 := by
      rw [h5]
      exact h9
    exact h10
  · -- If y > x, then max x y = y and min x y = x
    have h5 : max x y = y := by
      rw [max_eq_right (le_of_not_ge h4)]
    have h6 : min x y = x := by
      rw [min_eq_left (le_of_not_ge h4)]
    rw [h5, h6] at h₁ h₂
    have h7 : y = 22 * x + 2 := by
      rw [←Nat.div_add_mod y x, h₁, h₂]
      all_goals omega
    rw [h7] at h₀
    have h8 : x = 36 := by
      omega
    have h9 : y = 794 := by
      calc
        y = 22 * x + 2 := h7
        _ = 22 * 36 + 2 := by rw [h8]
        _ = 794 := by norm_num
    have h10 : max x y = 794 := by
      rw [h5]
      exact h9
    exact h10