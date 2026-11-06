import Mathlib

/-
Let $k$ be an integer such that $2 \le k \le 5$. Show that the digit 5 does not appear in the decimal representation of the number $(10^k-1)^2$.
-/

theorem number_theory_636721 (k:ℕ) (hk: 2 ≤ k ∧ k ≤ 5):
  5 ∉ Nat.digits 10 ((10 ^ k - 1) ^ 2 ) := by

  --We calculate every case directly.
  obtain ⟨kl,ku⟩ := hk
  interval_cases k <;> 
  norm_num