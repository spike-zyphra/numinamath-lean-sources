import Mathlib

theorem number_theory_6857 (x : ℤ) :
    (1296 * x ≡ 1125 [ZMOD 1935]) ↔
    (x ≡ 80 [ZMOD 1935]) ∨
    (x ≡ 295 [ZMOD 1935]) ∨
    (x ≡ 510 [ZMOD 1935]) ∨
    (x ≡ 725 [ZMOD 1935]) ∨
    (x ≡ 940 [ZMOD 1935]) ∨
    (x ≡ 1155 [ZMOD 1935]) ∨
    (x ≡ 1370 [ZMOD 1935]) ∨
    (x ≡ 1585 [ZMOD 1935]) ∨
    (x ≡ 1800 [ZMOD 1935]) := by
  apply Iff.intro
  · -- Assume 1296 * x ≡ 1125 [ZMOD 1935], prove the disjunction of the solutions
    intro h
    norm_num [Int.ModEq] at h ⊢
    have h2 : x % 1935 = 80 ∨ x % 1935 = 295 ∨ x % 1935 = 510 ∨ x % 1935 = 725 ∨ x % 1935 = 940 ∨ x % 1935 = 1155 ∨ x % 1935 = 1370 ∨ x % 1935 = 1585 ∨ x % 1935 = 1800 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2)
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
    · simp [Int.ModEq, h2]
  · -- Prove in the other direction: each congruence implies the original congruence
    rintro (h | h | h | h | h | h | h | h | h)
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega
    · norm_num [Int.ModEq] at h ⊢
      omega