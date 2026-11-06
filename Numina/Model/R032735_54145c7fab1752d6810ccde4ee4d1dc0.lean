import Mathlib

theorem number_theory_164840 (A B C D E F G H J : ℕ)
    (h₀ : A ∈ Set.Icc 1 9) (h₁ : B ∈ Set.Icc 0 9) (h₂ : C ∈ Set.Icc 1 9) 
    (h₃ : D ∈ Set.Icc 1 9) (h₄ : E ∈ Set.Icc 1 9) (h₅ : F ∈ Set.Icc 1 9)
    (h₆ : G ∈ Set.Icc 0 9) (h₇ : H ∈ Set.Icc 0 9) (h₈ : J ∈ Set.Icc 1 9)
    (h₉ : A ≠ B) (h₁₀ : A ≠ C) (h₁₁ : B ≠ C)
    (h₁₂ : (1000*A + 100*B + 10*A + C) * (100*A + 10*F + G) = D * 1111111)
    (h₁₃ : (1000*A + 100*B + 10*A + C) * (100*C + 10*H + B) = A * 1111111)
    (h₁₄ : (1000*A + 100*B + 10*A + C) * (100*F + 10*J + F) = E * 1111111)
    (h₁₅ : (1000*A + 100*B + 10*A + C) * (100*D + 10*E + C) = J * 1111111) :
    1 / (1000*A + 100*B + 10*A + C) = 2151 / 9999999 := by 
  ring_nf at h₁₂ h₁₃ h₁₄ h₁₅ ⊢
  simp [Nat.div_eq_of_eq_mul_left, Nat.mul_comm] at h₁₂ h₁₃ h₁₄ h₁₅ ⊢
  all_goals
    simp only [Set.mem_Icc] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    omega