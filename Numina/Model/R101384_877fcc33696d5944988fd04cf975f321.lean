import Mathlib

theorem algebra_100054 (n : ℤ) : n^5 - 5 * n^3 + 4 * n ≡ 0 [ZMOD 120] := by
  have h1 : n^5 - 5 * n^3 + 4 * n ≡ 0 [ZMOD 8] := by
    have h1 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [Int.ModEq, pow_succ, pow_zero, Int.add_emod, Int.sub_emod, Int.mul_emod, h] <;> ring_nf <;> omega

  have h2 : n^5 - 5 * n^3 + 4 * n ≡ 0 [ZMOD 3] := by
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h2 with (h | h | h) <;> simp [Int.ModEq, pow_succ, pow_zero, Int.add_emod, Int.sub_emod, Int.mul_emod, h] <;> ring_nf <;> omega

  have h3 : n^5 - 5 * n^3 + 4 * n ≡ 0 [ZMOD 5] := by
    have h3 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h3 with (h | h | h | h | h) <;> simp [Int.ModEq, pow_succ, pow_zero, Int.add_emod, Int.sub_emod, Int.mul_emod, h] <;> ring_nf <;> omega

  norm_num [Int.ModEq] at h1 h2 h3 ⊢
  omega