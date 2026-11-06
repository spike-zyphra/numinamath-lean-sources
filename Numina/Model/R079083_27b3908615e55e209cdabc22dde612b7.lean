import Mathlib

theorem algebra_284943 {a c : ℕ} (ha : 2^a = 8) (hc : a = 3 * c) : c = 1 := by
  have h1 : a = 3 := by
    exact Nat.pow_right_injective (by norm_num) ha
  rw [h1] at hc
  omega