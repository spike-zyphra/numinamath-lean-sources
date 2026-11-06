import Mathlib

theorem algebra_19199 (digits : List ℕ) (digits_def : digits = Nat.digits 10 ((1001001 * 1010101 + 989899 * 1001001) - (1001 * 989899) - (1010101 * 1001))) (a b : ℕ) (zeros : ∀ i < b, digits.getI i = 0) (rightmost : a ≠ 0 ∧ digits.getI b = a) : (a, b) = (2, 12) := by
  have h1 : (1001001 * 1010101 + 989899 * 1001001) - (1001 * 989899) - (1010101 * 1001) = 2000000000000 := by
    norm_num
  have h2 : digits = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] := by 
    rw [digits_def]
    rw [h1]
    norm_num
  have h3 : b = 12 := by
    have h4 : ∀ i < b, digits.getI i = 0 := zeros
    have h12 : b ≤ 12 := by
      by_contra h
      push_neg at h
      have h5 : digits.getI 12 = 2 := by 
        rw [h2]
        simp
      have h6 : digits.getI 12 = 0 := by 
        apply h4 12
        omega
      omega
    have h7 : b ≥ 12 := by
      by_contra h
      push_neg at h
      have h7 : b < 12 := by linarith
      have h8 : ∀ i < b, digits.getI i = 0 := zeros
      have h9 : b < 12 := h7
      interval_cases b <;> try { 
        simp [h2] at h8 rightmost ⊢ 
        all_goals try { 
          omega 
        } 
      }
    omega
  have ha : a = 2 := by 
    have hb12 : digits.getI b = a := by 
      tauto 
    rw [h3] at hb12
    have h30 : digits.getI 12 = 2 := by 
      rw [h2]
      simp 
    omega 
  simp [ha, h3]