import Mathlib

theorem number_theory_217609 (n : ℕ) (h₀ : Odd n) (h₁ : n^2 + (n+2)^2 + (n+4)^2 = 1111 ∨ n^2 + (n+2)^2 + (n+4)^2 = 2222 ∨ n^2 + (n+2)^2 + (n+4)^2 = 3333 ∨ n^2 + (n+2)^2 + (n+4)^2 = 4444 ∨ n^2 + (n+2)^2 + (n+4)^2 = 5555 ∨ n^2 + (n+2)^2 + (n+4)^2 = 6666 ∨ n^2 + (n+2)^2 + (n+4)^2 = 7777 ∨ n^2 + (n+2)^2 + (n+4)^2 = 8888 ∨ n^2 + (n+2)^2 + (n+4)^2 = 9999) :
    n = 41 := by
  rcases h₁ with (h | h | h | h | h | h | h | h | h)
  · -- Case 1: sum equals 1111
    have h2 : n ≤ 33 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 2: sum equals 2222
    have h2 : n ≤ 47 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 3: sum equals 3333
    have h2 : n ≤ 57 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 4: sum equals 4444
    have h2 : n ≤ 66 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 5: sum equals 5555
    have h2 : n ≤ 74 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 6: sum equals 6666
    have h2 : n ≤ 81 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 7: sum equals 7777
    have h2 : n ≤ 88 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 8: sum equals 8888
    have h2 : n ≤ 94 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega
  · -- Case 9: sum equals 9999
    have h2 : n ≤ 100 := by nlinarith [sq_nonneg (n : ℕ), sq_nonneg (n + 2 : ℕ), sq_nonneg (n + 4 : ℕ)]
    interval_cases n <;> norm_num at h₀ h <;> all_goals omega