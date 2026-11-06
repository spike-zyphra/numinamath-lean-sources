import Mathlib

theorem number_theory_113240 (n : ℕ) (hn : n ≠ 0) : 72 ∣ 9 ^ n + 63 := by 
  induction n with
  | zero =>
    exfalso 
    exact hn (by simp)
  | succ m ih =>
    cases m with 
    | zero =>
      norm_num
    | succ m =>
      have h_zero : m + 1 ≠ 0 := by positivity
      have h1 : 72 ∣ 9 ^ (m + 1) + 63 := ih h_zero
      have h2 : 9 ^ (m + 1 + 1) + 63 = (9 ^ (m + 1) * 9) + 63 := by ring
      rw [h2]
      omega