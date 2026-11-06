import Mathlib

theorem number_theory_60457 (p : ℕ) (hp : Nat.Prime p) (hp1 : p > 5) :
    ∃ m n, m + n < p ∧ p ∣ 2 ^ m * 3 ^ n - 1 := by
  use 0, 0
  constructor
  · -- Show m + n < p
    omega -- Since p > 5, p > 0
  · -- Show p divides 2 ^ 0 * 3 ^ 0 - 1
    have h2 : 2 ^ 0 * 3 ^ 0 - 1 = 0 := by
      omega 
    rw [h2]
    use 0 
    all_goals omega