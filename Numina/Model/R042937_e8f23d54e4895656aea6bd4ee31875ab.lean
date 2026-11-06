import Mathlib

theorem number_theory_6132 (n : ℤ) :
    n ≡ 0 [ZMOD 2] ∨ n ≡ 0 [ZMOD 3] ∨ n ≡ 1 [ZMOD 4] ∨ n ≡ 5 [ZMOD 6] ∨ n ≡ 7 [ZMOD 12] := by 
  have h5 : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 5 ∨ n % 12 = 6 ∨ n % 12 = 7 ∨ n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11 := by 
    omega
  rcases h5 with (h | h | h | h | h | h | h | h | h | h | h | h)
  · -- n ≡ 0 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 1 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 2 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 3 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 4 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 5 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 6 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 7 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 8 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 9 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 10 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega
  · -- n ≡ 11 [ZMOD 12]
    norm_num [Int.ModEq] at h ⊢
    omega