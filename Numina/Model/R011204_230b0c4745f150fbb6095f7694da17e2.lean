import Mathlib



theorem number_theory_233273 (a b c d e : ℕ) (h₀ : a + b + c + d + e = 200) :
    ¬(∃ k, k = a * b * c * d * e ∧ k % 10000 = 1999) := by
        by_contra h
        rcases h with ⟨k , hk⟩
        have hk₁ : k = a * b * c * d * e := by exact hk.1
        have hk₂ : k % 10000 = 1999 := by exact hk.2
        have h₁ : k % 2 = 1 := by
            omega
        have h₂ : (a * b * c * d * e) % 2 = 1 := by 
            rw [show k = a * b * c * d * e by exact hk₁] at h₁ 
            omega
        have h3 : a % 2 = 1 := by
            by_contra h
            push_neg at h
            have h4 : a % 2 = 0 := by omega
            have h5 : (a * b * c * d * e) % 2 = 0 := by
                simp [Nat.mul_mod, h4]
            omega
        have h4 : b % 2 = 1 := by
            by_contra h
            push_neg at h
            have h5 : b % 2 = 0 := by omega
            have h6 : (a * b * c * d * e) % 2 = 0 := by
                simp [Nat.mul_mod, h5]
            omega
        have h5 : c % 2 = 1 := by
            by_contra h
            push_neg at h
            have h6 : c % 2 = 0 := by omega
            have h7 : (a * b * c * d * e) % 2 = 0 := by
                simp [Nat.mul_mod, h6]
            omega
        have h6 : d % 2 = 1 := by
            by_contra h
            push_neg at h
            have h7 : d % 2 = 0 := by omega
            have h8 : (a * b * c * d * e) % 2 = 0 := by
                simp [Nat.mul_mod, h7]
            omega
        have h7 : e % 2 = 1 := by
            by_contra h
            push_neg at h
            have h8 : e % 2 = 0 := by omega
            have h9 : (a * b * c * d * e) % 2 = 0 := by
                simp [Nat.mul_mod, h8]
            omega
        have h8 : (a + b + c + d + e) % 2 = 1 := by
            omega
        omega