import Mathlib

theorem algebra_156458 {n : ℕ} (h : n + (Nat.digits 10 n).sum = 328) : n = 317 := by
  have h1 : n ≤ 328 := by
    have hsum : (Nat.digits 10 n).sum ≥ 0 := by positivity
    linarith
  interval_cases n <;> norm_num at h ⊢ <;> all_goals omega