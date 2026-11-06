import Mathlib

theorem number_theory_113555 (n : ℕ) : 13 * (-50 : ℤ)^n + 17 * 40^n - 30 ≡ 0 [ZMOD 1989] := by
  have h1 : ∀ (n : ℕ), (13 * (-50 : ℤ) ^ n + 17 * 40 ^ n - 30 : ℤ) % 1989 = 0 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      norm_num [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_succ] at ih ⊢
      omega
  simp [Int.ModEq] at *
  have h2 := h1 n 
  omega