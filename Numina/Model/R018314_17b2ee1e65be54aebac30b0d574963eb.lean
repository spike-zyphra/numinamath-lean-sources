import Mathlib

theorem algebra_167692 (emil heinz father mother : ℕ)
    (h₀ : heinz = emil / 2) (h₁ : father = heinz ^ 2) (h₂ : mother = father - 5)
    (h₃ : emil + heinz + father + mother = 85) :
    emil = 12 := by 
  have h4 : emil ≤ 85 := by 
    omega
  have h5 : emil ≤ 15 := by
    by_contra h
    push_neg at h
    have h6 : heinz ≥ 8 := by
      rw [h₀]
      omega
    have h7 : father ≥ 64 := by
      rw [h₁]
      have h8 : heinz ≥ 8 := by
        omega
      have h9 : heinz ^ 2 ≥ 64 := by
        have h10 : heinz ≥ 8 := by 
          omega
        have h11 : heinz ≥ (8 : ℕ) := by
          omega
        have h12 : heinz ^ 2 ≥ (8 : ℕ) ^ 2 := by
          apply Nat.pow_le_pow_left
          all_goals omega
        nlinarith
      nlinarith
    have h9 : mother = father - 5 := by
      exact h₂
    omega
  interval_cases emil <;> simp [h₀, h₁, h₂] at h₃ <;> omega