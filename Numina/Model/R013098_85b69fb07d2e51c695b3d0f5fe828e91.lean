import Mathlib

theorem algebra_19702 {x : ℕ} : (2^(x + 1))^3 * 4^x = 8192 ↔ x = 2 := by
  constructor
  · -- Assume (2^(x + 1))^3 * 4^x = 8192 prove x = 2
    intro h
    have eq1 : (2 ^ (x + 1)) ^ 3 * 4 ^ x = 2 ^ (5 * x + 3) := by
      have h1 : (2 ^ (x + 1)) ^ 3 = 2 ^ (3 * (x + 1)) := by
        ring_nf
      have h2 : 4 ^ x = 2 ^ (2 * x) := by
        rw [show 4 = 2 ^ 2 by norm_num]
        rw [← pow_mul]
      calc
        (2 ^ (x + 1)) ^ 3 * 4 ^ x = 2 ^ (3 * (x + 1)) * 2 ^ (2 * x) := by
          rw [h1, h2]
        _ = 2 ^ (3 * (x + 1) + 2 * x) := by
          rw [← pow_add]
        _ = 2 ^ (5 * x + 3) := by
          ring_nf
    rw [eq1] at h
    have h2 : 5 * x + 3 = 13 := by
      have h3 : 2 ^ (5 * x + 3) = 2 ^ 13 := by
        exact h
      have h4 : 5 * x + 3 = 13 := by
        exact Nat.pow_right_injective (by norm_num) h3
      exact h4
    have h3 : 5 * x = 10 := by 
      omega
    have h4 : x = 2 := by
      omega
    exact h4
  · -- Assume x = 2 prove (2^(x + 1))^3 * 4^x = 8192
    rintro h
    rw [h]
    all_goals norm_num