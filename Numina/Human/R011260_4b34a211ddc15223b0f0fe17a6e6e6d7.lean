import Mathlib


/-What is the smallest positive integer $m$ such that $\frac{10!}{m}$ is a perfect square?-/
theorem number_theory_614398 : IsLeast {m : ℕ | 0 < m ∧ ∃ k : ℕ, (Nat.factorial 10 : ℚ) / m = k ^ 2} 7 := by
  simp [IsLeast, lowerBounds]; constructor
  -- Show that $10!/7=720^2$
  · use 720; norm_num [show Nat.factorial 10 = 3628800 by rfl]
  intro m mpos k hk; by_contra!
-- Prove that all the numbers less than $7$ fail to satisfy the property in question
  interval_cases m; all_goals norm_num [show Nat.factorial 10 = 3628800 by rfl] at hk
  all_goals norm_cast at hk
  · replace hk : 1904 ^ 2 < k ^ 2 ∧ k ^ 2 < 1905 ^ 2 := by omega
    rw [Nat.pow_lt_pow_iff_left, Nat.pow_lt_pow_iff_left] at hk
    all_goals omega
  · replace hk : 1346 ^ 2 < k ^ 2 ∧ k ^ 2 < 1347 ^ 2 := by omega
    rw [Nat.pow_lt_pow_iff_left, Nat.pow_lt_pow_iff_left] at hk
    all_goals omega
  · replace hk : 1099 ^ 2 < k ^ 2 ∧ k ^ 2 < 1100 ^ 2 := by omega
    rw [Nat.pow_lt_pow_iff_left, Nat.pow_lt_pow_iff_left] at hk
    all_goals omega
  · replace hk : 952 ^ 2 < k ^ 2 ∧ k ^ 2 < 953 ^ 2 := by omega
    rw [Nat.pow_lt_pow_iff_left, Nat.pow_lt_pow_iff_left] at hk
    all_goals omega
  · replace hk : 851 ^ 2 < k ^ 2 ∧ k ^ 2 < 852 ^ 2 := by omega
    rw [Nat.pow_lt_pow_iff_left, Nat.pow_lt_pow_iff_left] at hk
    all_goals omega
  replace hk : 777 ^ 2 < k ^ 2 ∧ k ^ 2 < 778 ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left, Nat.pow_lt_pow_iff_left] at hk
  all_goals omega