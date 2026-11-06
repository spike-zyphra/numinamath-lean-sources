import Mathlib

theorem number_theory_106429 :
    ∀ n : ℤ, n^2 ≡ 0 [ZMOD 9] ∨ n^2 ≡ 1 [ZMOD 3] := by
  intro n
  have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by 
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h)
  · -- Case n ≡ 0 [ZMOD 9]
    have h2 : n^2 % 9 = 0 := by
      simp [pow_two, Int.mul_emod, h]
    left
    simp [Int.ModEq, h2]
  · -- Case n ≡ 1 [ZMOD 9]
    have h2 : n^2 % 9 = 1 := by
      simp [pow_two, Int.mul_emod, h]
    right
    simp [Int.ModEq]
    have h3 : n^2 % 3 = 1 := by
      omega
    simp [Int.ModEq, h3]
  · -- Case n ≡ 2 [ZMOD 9]
    have h2 : n^2 % 9 = 4 := by
      simp [pow_two, Int.mul_emod, h]
    right
    simp [Int.ModEq]
    have h3 : n^2 % 3 = 1 := by
      omega
    simp [Int.ModEq, h3]
  · -- Case n ≡ 3 [ZMOD 9]
    have h2 : n^2 % 9 = 0 := by
      simp [pow_two, Int.mul_emod, h]
    left
    simp [Int.ModEq, h2]
  · -- Case n ≡ 4 [ZMOD 9]
    have h2 : n^2 % 9 = 7 := by
      simp [pow_two, Int.mul_emod, h]
    right
    simp [Int.ModEq]
    have h3 : n^2 % 3 = 1 := by
      omega
    simp [Int.ModEq, h3]
  · -- Case n ≡ 5 [ZMOD 9]
    have h2 : n^2 % 9 = 7 := by
      simp [pow_two, Int.mul_emod, h]
    right
    simp [Int.ModEq]
    have h3 : n^2 % 3 = 1 := by
      omega
    simp [Int.ModEq, h3]
  · -- Case n ≡ 6 [ZMOD 9]
    have h2 : n^2 % 9 = 0 := by
      simp [pow_two, Int.mul_emod, h]
    left
    simp [Int.ModEq, h2]
  · -- Case n ≡ 7 [ZMOD 9]
    have h2 : n^2 % 9 = 4 := by
      simp [pow_two, Int.mul_emod, h]
    right
    simp [Int.ModEq]
    have h3 : n^2 % 3 = 1 := by
      omega
    simp [Int.ModEq, h3]
  · -- Case n ≡ 8 [ZMOD 9]
    have h2 : n^2 % 9 = 1 := by
      simp [pow_two, Int.mul_emod, h]
    right
    simp [Int.ModEq]
    have h3 : n^2 % 3 = 1 := by
      omega
    simp [Int.ModEq, h3]