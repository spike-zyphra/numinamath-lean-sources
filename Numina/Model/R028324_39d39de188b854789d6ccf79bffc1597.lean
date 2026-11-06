import Mathlib

theorem Other_24296 (k : ℕ) (hk : 1 < k) :
  ∃ j : ℕ, k ∣ j ∧ j < k ^ 4 ∧
    Finset.card (Nat.digits 10 j).toFinset ≤ 4 := by
  use 0
  constructor
  · -- Show that k divides 0, which is trivially true since any natural number divides 0.
    exact dvd_zero k 
  constructor 
  · -- Show that 0 < k^4. Since k > 1, k is at least 2, so k^4 is at least 16.
    have h1 : k ^ 4 > 0 := by
      apply Nat.pow_pos
      linarith
    linarith 
  · -- Show that Finset.card (Nat.digits 10 0).toFinset ≤ 4
    simp