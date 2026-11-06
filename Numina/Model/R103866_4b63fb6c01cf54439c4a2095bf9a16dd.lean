import Mathlib

theorem number_theory_139681 (n : ℤ) :
    n ≡ 3 [ZMOD 5] ∧ n ≡ 4 [ZMOD 7] ∧ n ≡ 5 [ZMOD 3] ↔
    ∃ k, n = 105 * k + 53 := by
  constructor
  · -- Assume (n ≡ 3 [ZMOD 5] ∧ n ≡ 4 [ZMOD 7] ∧ n ≡ 5 [ZMOD 3]), prove ∃ k, n = 105 * k + 53
    rintro ⟨h1, h2, h3⟩
    use (n - 53) / 105
    -- First congruence
    norm_num [Int.ModEq] at h1 h2 h3 ⊢
    omega
  · -- Assume ∃ k, n = 105 * k + 53, prove n ≡ 3 [ZMOD 5] ∧ n ≡ 4 [ZMOD 7] ∧ n ≡ 5 [ZMOD 3]
    rintro ⟨k, hk⟩
    constructor
    · -- n ≡ 3 [ZMOD 5]
      norm_num [Int.ModEq] at *
      omega
    constructor
    · -- n ≡ 4 [ZMOD 7]
      norm_num [Int.ModEq] at *
      omega
    · -- n ≡ 5 [ZMOD 3]
      norm_num [Int.ModEq] at *
      omega