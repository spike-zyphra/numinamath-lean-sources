import Mathlib

theorem number_theory_23076 {a b : ℕ} (ha : a * 3 ≡ 1 [MOD 19]) (hb : b * 13 ≡ 1 [MOD 19]) : a + b ≡ 16 [MOD 19] := by
  norm_num [Nat.ModEq] at ha hb ⊢
  have h1 : a % 19 = 13 := by
    omega
  have h2 : b % 19 = 3 := by
    omega
  omega