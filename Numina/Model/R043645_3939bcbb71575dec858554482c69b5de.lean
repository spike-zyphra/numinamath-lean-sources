import Mathlib

theorem number_theory_22850 {a b : ℤ} (h : a * b ≡ 17 [ZMOD 20]) :
    (a + 10) * (b + 10) ≡ 17 [ZMOD 20] := by
  have h1 : a * b % 20 = 17 := h
  have h4 : (a + 10) * (b + 10) % 20 = 17 := by
    have h7 : (a + 10) * (b + 10) = a * b + 10 * (a + b) + 100 := by ring
    rw [h7]
    have h100 : a * b % 4 = 1 := by 
      omega
    have h3 : a % 2 = 1 := by
      by_contra h3
      push_neg at h3
      have h4 : a % 2 = 0 := by omega
      have h5 : (a * b) % 2 = 0 := by
        have h6 : a % 2 = 0 := h4
        have h7 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases h7 with (h7 | h7)
        · -- b even
          have h8 : b % 2 = 0 := h7
          simp [Int.mul_emod, h6, h8]
        · -- b odd
          have h8 : b % 2 = 1 := h7
          simp [Int.mul_emod, h6, h8]
      omega
    have h4 : b % 2 = 1 := by
      by_contra h4
      push_neg at h4
      have h5 : b % 2 = 0 := by omega
      have h6 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases h6 with (h6 | h6)
      · -- a even
        have h7 : a % 2 = 0 := h6
        have h8 : b % 2 = 0 := h5
        have h9 : (a * b) % 2 = 0 := by
          simp [Int.mul_emod, h7, h8]
        omega
      · -- a odd
        have h7 : a % 2 = 1 := h6
        have h8 : b % 2 = 0 := h5
        have h9 : (a * b) % 2 = 0 := by
          simp [Int.mul_emod, h7, h8]
        omega
    have h11 : (a + b) % 2 = 0 := by
      omega
    have h12 : (10 * (a + b) : ℤ) % 20 = 0 := by
      have h13 : (a + b) % 2 = 0 := h11
      omega
    omega
  show (a + 10) * (b + 10) ≡ 17 [ZMOD 20]
  simp [Int.ModEq, h4]