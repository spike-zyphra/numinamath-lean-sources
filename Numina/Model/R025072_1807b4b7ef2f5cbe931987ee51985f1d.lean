import Mathlib

theorem number_theory_187604 (n : ℤ) :
    13 ∣ n^2 - 6 * n - 4 ↔ n ≡ 3 [ZMOD 13] := by
  constructor
  · -- Assume 13 divides n^2 - 6 * n - 4, prove n ≡ 3 [ZMOD 13]
    intro h
    have h4 : (n ^ 2 - 6 * n - 4 : ℤ) % 13 = 0 := by
      omega
    have h3 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [Int.ModEq, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h3] at h4 ⊢
    <;> omega
  · -- Assume n ≡ 3 [ZMOD 13], prove 13 divides n^2 - 6 * n - 4
    intro h
    have h4 : n % 13 = 3 := by
      simp [Int.ModEq] at h ⊢
      omega
    have h5 : (n ^ 2 - 6 * n - 4 : ℤ) % 13 = 0 := by
      have h4' : n % 13 = 3 := h4
      simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, h4']
    omega