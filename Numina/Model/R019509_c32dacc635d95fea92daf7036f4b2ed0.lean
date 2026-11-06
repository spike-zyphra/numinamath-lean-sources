import Mathlib

theorem number_theory_291188 (n : ℕ) (h₀ : n < 1000) (h₁ : n > 99)
    (h₂ : n / (n % 100) = 9 ∧ n % (n % 100) = 8) :
    n = 224 ∨ n = 449 ∨ n = 674 ∨ n = 899 := by 
  rcases h₂ with ⟨h₃, h₄⟩ 
  have h₅ : n % 100 > 0 := by 
    by_contra h 
    push_neg at h 
    have h₆ : n % 100 = 0 := by 
      omega 
    rw [h₆] at h₃ h₄ 
    all_goals omega
  have h₆ : n % 100 ≤ 99 := by 
    omega 
  have eq1 : n = 9 * (n % 100) + 8 := by 
    have h₈ : n % (n % 100) + (n % 100) * (n / (n % 100)) = n := by 
      have h₉ : n % (n % 100) + (n % 100) * (n / (n % 100)) = n := by 
        rw [Nat.mod_add_div n (n % 100)]
        <;> ring 
      linarith 
    rw [h₃, h₄] at h₈ 
    have h₉ : (n % 100) * 9 + 8 = n := by 
      omega 
    linarith 
  interval_cases h8 : n % 100 <;> omega