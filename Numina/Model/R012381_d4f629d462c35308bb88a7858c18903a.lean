import Mathlib

theorem algebra_5402 {m n : ℕ} : ¬(m^2 + n^2 = (m + 1) * (n + 1)) := by
  rintro h
  have eq1 : m ≤ 3 := by
    nlinarith [sq_nonneg (m - n : ℤ), sq_nonneg (m - 2 : ℤ), sq_nonneg (n - 2 : ℤ),
      h, sq_nonneg ((m : ℤ) - (n : ℤ)), sq_nonneg ((m + 1 : ℤ) - (n + 1 : ℤ)), sq_nonneg ((m : ℤ) - (n : ℤ))]
  have eq2 : n ≤ 3 := by
    nlinarith [sq_nonneg (m - n : ℤ), sq_nonneg (m - 2 : ℤ), sq_nonneg (n - 2 : ℤ),
      h, sq_nonneg ((m : ℤ) - (n : ℤ)), sq_nonneg ((m + 1 : ℤ) - (n + 1 : ℤ)), sq_nonneg ((m : ℤ) - (n : ℤ))]
  interval_cases m <;> interval_cases n <;> omega