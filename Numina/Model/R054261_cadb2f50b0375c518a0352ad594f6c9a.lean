import Mathlib

theorem number_theory_5517 (n : ℕ) (h : n > 0) :
    Nat.ofDigits n [2, 4] * Nat.ofDigits n [1, 3] = Nat.ofDigits n [2, 3, 6, 1] ↔ n = 7 := by
  simp [Nat.ofDigits, List.foldl] at *
  constructor
  · -- If (4n + 2)(3n + 1) = n^3 + 6n^2 + 3n + 2 then n = 7
    intro h_eq
    have h1 : n ≤ 7 := by
      nlinarith [sq_nonneg (n - 7 : ℤ), sq_nonneg (n * n - 1 : ℤ), sq_nonneg ((n + 1 : ℤ) * (n - 7 : ℤ)), sq_nonneg (n - 1 : ℤ), sq_nonneg (n * (n - 7 : ℤ)), sq_nonneg ((n - 7 : ℤ) * (n : ℤ)), sq_nonneg (n * (n + 1 : ℤ)), sq_nonneg ((n * n - n + 2 : ℤ)), sq_nonneg ((n - 7 : ℤ)), sq_nonneg (n + 1 : ℤ), sq_nonneg ((n - 7 : ℤ) * (n + 1 : ℤ)), sq_nonneg ((n : ℤ) - 1), sq_nonneg ((n : ℤ) - 7)]
    interval_cases n <;> omega
  · -- If n = 7 then (4n + 2)(3n + 1) = n^3 + 6n^2 + 3n + 2
    intro heq
    rw [heq]
    <;> norm_num
    all_goals
      try omega
      try nlinarith
      try { tauto } <;> try { nlinarith }