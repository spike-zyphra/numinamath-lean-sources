import Mathlib

theorem number_theory_46991 : ¬∃ n, n^3 = 10^49 + 5 * 10^99 + 1 := by
  rintro ⟨n, hn⟩
  have h1 : n^3 % 13 = (10^49 + 5 * 10^99 + 1) % 13 := by
    omega
  norm_num at h1 hn
  have h2 : n^3 % 13 = 0 ∨ n^3 % 13 = 1 ∨ n^3 % 13 = 5 ∨ n^3 % 13 = 8 ∨ n^3 % 13 = 12 := by
    have h : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by
      omega
    rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Nat.mul_mod] at *
  omega