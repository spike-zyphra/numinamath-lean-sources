import Mathlib

theorem number_theory_285883 (a : ℤ) : 
    (8 ∣ (5 * a + 3) * (3 * a + 1)) → (16 ∣ (5 * a + 3) * (3 * a + 1)) := by
  intro h
  have h1 : a % 8 = 1 ∨ a % 8 = 5 := by
    have h2 : (5 * a + 3) * (3 * a + 1) % 8 = 0 := by 
      omega
    have h3 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [Int.add_emod, Int.mul_emod, h3] at h2 <;> tauto
  rcases h1 with (h1 | h1)
  · -- a ≡ 1 (mod 8)
    have h4 : a % 16 = 1 ∨ a % 16 = 9 := by
      omega
    rcases h4 with (h4 | h4)
    · -- a ≡ 1 (mod 16)
      have h5 : (5 * a + 3) * (3 * a + 1) % 16 = 0 := by
        have h6 : a % 16 = 1 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h6]
      omega
    · -- a ≡ 9 (mod 16)
      have h5 : (5 * a + 3) * (3 * a + 1) % 16 = 0 := by
        have h6 : a % 16 = 9 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h6]
      omega
  · -- a ≡ 5 (mod 8)
    have h4 : a % 16 = 5 ∨ a % 16 = 13 := by
      omega
    rcases h4 with (h4 | h4)
    · -- a ≡ 5 (mod 16)
      have h5 : (5 * a + 3) * (3 * a + 1) % 16 = 0 := by
        have h6 : a % 16 = 5 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h6]
      omega
    · -- a ≡ 13 (mod 16)
      have h5 : (5 * a + 3) * (3 * a + 1) % 16 = 0 := by
        have h6 : a % 16 = 13 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h6]
      omega