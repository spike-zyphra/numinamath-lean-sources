import Mathlib

theorem algebra_193775 (n : ℕ) :
    (∑ i ∈ Finset.range 9, 9^n) = 3^2012 ↔ n = 1005 := by
  constructor
  · -- Forward direction: if the equation holds, then n = 1005
    intro h
    have h1 : (∑ i in Finset.range 9, 9 ^ n) = 9 * (9 ^ n) := by 
      simp [Finset.sum_range_succ, Finset.sum_range_zero, add_assoc]
      <;> ring
    rw [h1] at h
    have h2 : 9 * (9 ^ n) = 3 ^ (2 * (n + 1 : ℕ)) := by
      rw [show 9 = 3 ^ 2 by norm_num]
      rw [← pow_mul]
      <;> ring_nf
    rw [h2] at h
    have h3 : 2 * (n + 1) = 2012 := by
      have h4 : 3 ^ (2 * (n + 1 : ℕ)) = 3 ^ (2012 : ℕ) := by
        exact_mod_cast h
      have h5 : 2 * (n + 1 : ℕ) = (2012 : ℕ) := by
        exact Nat.pow_right_injective (by norm_num) h4
      exact_mod_cast h5
    have h4 : n = 1005 := by
      omega
    exact h4
  · -- Backward direction: if n = 1005, then the equation holds
    intro h
    rw [h]
    native_decide