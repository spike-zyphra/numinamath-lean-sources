import Mathlib

theorem algebra_20253 {n : ℕ} (h : n % 2 = 1) (h' : (n + 2) % 2 = 1)
    (h'' : |(n^2 : ℤ) - (n + 2)^2| = 128) :
    n * (n + 2) = 1023 := by
  have h1 : (n : ℤ) % 2 = 1 := by exact_mod_cast h
  have h2 : (n + 2 : ℤ) % 2 = 1 := by exact_mod_cast h'
  have h3 : (n : ℤ)^2 - (n + 2 : ℤ)^2 = -4 * (n : ℤ) - 4 := by
    ring
  have h4 : |(n : ℤ)^2 - (n + 2 : ℤ)^2| = 128 := by
    simpa using h''
  have h5 : |(n : ℤ)^2 - (n + 2 : ℤ)^2| = |(-4 * (n : ℤ) - 4)| := by
    rw [h3]
  rw [h5] at h4
  cases' eq_or_eq_neg_of_abs_eq h4 with h6 h7
  · -- Case where -4n - 4 = 128
    have h8 : (n : ℤ) = -33 := by
      linarith
    have h9 : (n : ℤ) * (n + 2 : ℤ) = 1023 := by
      rw [h8]
      norm_num
    have h10 : n * (n + 2) = 1023 := by
      norm_cast at h9 ⊢
    exact h10
  · -- Case where -4n - 4 = -128
    have h8 : (n : ℤ) = 31 := by
      linarith
    have h9 : (n : ℤ) * (n + 2 : ℤ) = 1023 := by
      rw [h8]
      norm_num
    have h10 : n * (n + 2) = 1023 := by
      norm_cast at h9 ⊢
    exact h10