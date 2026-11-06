import Mathlib

theorem algebra_287703 {a b c d : ℕ} (h₀ : a + b + c + d = 243)
    (h₁ : a + 8 = b - 8) (h₂ : b - 8 = c * 8) (h₃ : c * 8 = d / 8) :
    max (max a c) (max b d) * min (min a c) (min b d) = 576 := by 
  have h4 : b = 8 * c + 8 := by
    omega
  have h5 : a = 8 * c - 8 := by
    omega
  have h6 : d = 64 * c := by
    have h7 : d = 64 * c := by
      omega
    omega
  have h7 : c = 3 := by
    omega
  have h8 : a = 16 := by
    omega
  have h9 : b = 32 := by
    omega
  have h10 : d = 192 := by
    omega
  simp [h8, h9, h7, h10]
  all_goals try { omega }