import Mathlib

theorem algebra_271957 (A B C D : ℕ) (h₀ : A ≠ 0) (h₁ : A ≤ 9) (h₂ : B ≤ 9) (h₃ : C ≤ 9) (h₄ : D ≤ 9)
    (h₅ : 1000 * A + 100 * B + 10 * C + D = 2023) :
    A * B + C * D = 6 := by
  have h6 : A ≤ 2 := by 
    omega 
  have h7 : A = 1 ∨ A = 2 := by
    omega 
  cases h7 with
  | inl hA1 =>
    omega 
  | inr hA2 =>
    have h10 : 100 * B + 10 * C + D = 23 := by
      have : 1000 * A + 100 * B + 10 * C + D = 2023 := h₅
      rw [show A = 2 by exact hA2] at this
      omega
    have h11 : B = 0 := by
      by_cases hB : B > 0
      · have : 100 * B ≥ 100 := by 
          nlinarith 
        have : 100 * B + 10 * C + D ≥ 100 := by 
          omega 
        linarith
      · have : B = 0 := by 
          omega 
        exact this 
    have h12 : 10 * C + D = 23 := by 
      rw [show B = 0 by exact h11] at h10 
      omega 
    have h13 : C = 2 := by 
      by_cases hC : C > 2
      · have : 10 * C ≥ 30 := by 
          nlinarith 
        have : 10 * C + D ≥ 30 := by 
          omega 
        linarith 
      · have : C ≤ 2 := by 
          omega 
        interval_cases C <;> 
        try { omega } <;> 
        try { 
          simp at h12 
          all_goals omega 
        }
    have h14 : D = 3 := by
      rw [show C = 2 by exact h13] at h12 
      omega 
    simp [hA2, h11, h13, h14]
    all_goals omega