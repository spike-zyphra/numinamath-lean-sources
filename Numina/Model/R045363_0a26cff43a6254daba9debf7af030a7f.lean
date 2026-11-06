import Mathlib

theorem algebra_229830 {a b c : ℤ} (h₀ : b^2 = a * c) (h₁ : 2*(b+8) = a+c) (h₂ : (b + 8)^2 = a * (c+64)) :
    a = 4 ∧ b = 12 ∧ c = 36 := by

  have h3 : a = 2 * (b + 8) - c := by 
    linarith 
  rw [h3] at h₀ h₂ 
  have eq3 : (b - c) ^ 2 = 16 * c := by 
    nlinarith 
  have eq4 : (b - c) ^ 2 - 112 * b + 48 * c - 960 = 0 := by 
    nlinarith 
  have eq5 : 4 * c = 7 * b + 60 := by 
    nlinarith [eq3, eq4] 
  have eq6 : b = 12 := by
    have h4 : (b : ℤ) % 4 = 0 := by
      omega 
    have eq8 : (b - 12) * (9 * b + 20) = 0 := by
      have eq9 : 9 * b ^ 2 - 88 * b - 240 = 0 := by
        have eq3' : (b - c) ^ 2 = 16 * c := eq3 
        have eq10 : 4 * c = 7 * b + 60 := eq5 
        have eq6 : 9 * b ^ 2 - 88 * b - 240 = 0 := by
          have h3c : 4 * c = 7 * b + 60 := eq10 
          nlinarith [sq_nonneg (b - 12), sq_nonneg (c - 36), h3c, sq_nonneg (4 * (b - 12)), sq_nonneg (c * 4)]
        linarith 
      linarith 
    cases' (mul_eq_zero.mp eq8) with h9 h10 
    · -- case b-12 =0 
      linarith 
    · -- case 9b+20=0 
      omega 
  have eq7 : c = 36 := by
    rw [eq6] at eq5
    omega
  have eq8 : a = 4 := by 
    rw [eq7] at h3 
    rw [eq6] at h3 
    linarith 
  exact ⟨eq8, eq6, eq7⟩