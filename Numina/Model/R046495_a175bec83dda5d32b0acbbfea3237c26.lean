import Mathlib

theorem algebra_105251 {a b c : ℕ} (h₀ : a + b + c = 3053)
    (h₁ : a / (b / 2) = 3 ∧ a % (b / 2) = 5) (h₂ : c / (b / 4) = 5 ∧ c % (b / 4) = 3) :
    a = 1223 ∧ b = 812 ∧ c = 1018 := by

  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩

  have h4 : a = 3 * (b / 2) + 5 := by
    rw [←Nat.div_add_mod a (b / 2)]
    rw [h₁₁, h₁₂]
    all_goals omega

  have h5 : c = 5 * (b / 4) + 3 := by
    by_cases h6 : b / 4 > 0
    · -- Use the division theorem, since b / 4 > 0.
      rw [←Nat.div_add_mod c (b / 4)]
      rw [h₂₁, h₂₂]
      all_goals omega
    · -- Assume b / 4 = 0.
      have h7 : b / 4 = 0 := by
        omega
      have h8 : c / (b / 4) = 0 := by
        rw [h7]
        norm_num
      omega -- This will derive False from h₂₁ (c/(b/4) =5) and h8 (c/(b/4)=0).

  rw [h4, h5] at h₀

  have h10 : b = 812 := by 
    omega

  have h7 : a = 1223 := by 
    rw [h10] at h4
    omega

  have h8 : c = 1018 := by 
    rw [h10] at h5
    omega

  exact ⟨h7, h10, h8⟩