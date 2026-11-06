import Mathlib

theorem number_theory_6488 (m : ℤ) (h₀ : IsSquare (2*m + 1)) (h₁ : IsSquare (3*m + 1)) :
    40 ∣ m := by
  have h2 : (2 * m + 1) % 8 = 0 ∨ (2 * m + 1) % 8 = 1 ∨ (2 * m + 1) % 8 = 4 := by
    rcases h₀ with ⟨x, hx⟩
    have h3 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by
      have h2 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2, Int.ofNat]
    have h4 : (2 * m + 1) % 8 = x^2 % 8 := by 
      rw [show (2 * m + 1 : ℤ) = x^2 by 
        nlinarith [hx]
      ]
    rw [h4]
    tauto
  have h4 : (3 * m + 1) % 8 = 0 ∨ (3 * m + 1) % 8 = 1 ∨ (3 * m + 1) % 8 = 4 := by 
    rcases h₁ with ⟨y, hy⟩ 
    have h2 : y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4 := by 
      have h3 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by omega 
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h3, Int.ofNat]
    have h5 : (3 * m + 1) % 8 = y^2 % 8 := by 
      rw [show (3 * m + 1 : ℤ) = y^2 by 
        nlinarith [hy]
      ]
    rw [h5]
    tauto
  have h5 : (2 * m + 1) % 5 = 0 ∨ (2 * m + 1) % 5 = 1 ∨ (2 * m + 1) % 5 = 4 := by
    rcases h₀ with ⟨x, hx⟩ 
    have h3'' : (2 * m + 1) % 5 = x^2 % 5 := by 
      rw [show (2 * m + 1 : ℤ) = x^2 by 
        nlinarith [hx]
      ]
    rw [h3''] at *
    have h2 : x^2 % 5 = 0 ∨ x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by 
      have h3 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega 
      rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h3]
    tauto
  have h6 : (3 * m + 1) % 5 = 0 ∨ (3 * m + 1) % 5 = 1 ∨ (3 * m + 1) % 5 = 4 := by
    rcases h₁ with ⟨y, hy⟩ 
    have h4'' : (3 * m + 1) % 5 = y^2 % 5 := by
      rw [show (3 * m + 1 : ℤ) = y^2 by 
        nlinarith [hy]
      ]
    rw [h4''] at *
    have h2 : y^2 % 5 = 0 ∨ y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by 
      have h3 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by omega 
      rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h3]
    tauto 
  omega