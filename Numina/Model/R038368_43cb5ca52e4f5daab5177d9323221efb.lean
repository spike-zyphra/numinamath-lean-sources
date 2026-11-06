import Mathlib

theorem number_theory_286385 {A B C : ℕ} (h₀ : A / B = C) (h₁ : A % B = 8) (h₂ : A + B + C = 2994) :
    A = 8 ∨ A = 2864 := by
  have h3 : B ≠ 0 := by
    by_contra h
    have h4 : B = 0 := by omega
    simp [h4] at h₀ h₁
    all_goals omega

  have h4 : A = B * C + 8 := by 
    rw [←Nat.div_add_mod A B]
    rw [h₀, h₁]
    all_goals linarith

  -- Substitute $A = B * C + 8$ into $A + B + C = 2994$
  have h5 : B * C + 8 + B + C = 2994 := by
    linarith [h₂, h4]

  have h6 : B * C + B + C = 2986 := by
    omega

  have h7 : (B + 1) * (C + 1) = 2987 := by 
    nlinarith

  have h8 : (B + 1) ∣ 2987 := by 
    use (C + 1)
    all_goals linarith

  have h10 : (B + 1) = 1 ∨ (B + 1) = 29 ∨ (B + 1) = 103 ∨ (B + 1) = 2987 := by
    have h11 : (B + 1) ∣ 2987 := h8
    have h12 : (B + 1) ≤ 2987 := by 
      exact Nat.le_of_dvd (by norm_num) h11
    interval_cases h : (B + 1) <;> norm_num at h11 ⊢ <;> omega

  rcases h10 with (h11 | h11 | h11 | h11)
  · -- B + 1 = 1 
    exfalso
    have h12 : B = 0 := by omega
    contradiction

  · -- B + 1 = 29
    have h13 : B = 28 := by omega
    have h14 : (C + 1) = 103 := by
      nlinarith
    have h15 : C = 102 := by omega
    have h16 : A = 2864 := by 
      rw [h13, h15] at h4
      omega
    right
    exact h16

  · -- B + 1 = 103
    have h13 : B = 102 := by omega
    have h14 : (C + 1) = 29 := by
      nlinarith
    have h15 : C = 28 := by omega
    have h16 : A = 2864 := by 
      rw [h13, h15] at h4
      omega
    right
    exact h16

  · -- B + 1 = 2987
    have h13 : B = 2986 := by omega
    have h14 : (C + 1) = 1 := by 
      nlinarith
    have h15 : C = 0 := by omega
    have h16 : A = 8 := by 
      rw [h13, h15] at h4
      omega
    left
    exact h16