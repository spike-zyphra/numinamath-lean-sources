import Mathlib

/-calculate at x = 7
(x - 4) ^ (x - 5) ^ (x - 6) ^ (x + 6) ^ (x + 5) -/

theorem algebra_292019 {x: ℕ} (hx: x = 7):
  (x - 4) ^ (x - 5) ^ (x - 6) ^ (x + 6) ^ (x + 5) = 9 := by
    
    have o: (x - 6) ^ (x + 6) ^ (x + 5) = 1 := by
      rw [hx]
      rw [show 7 - 6 = 1 by rfl]
      apply Nat.one_pow
    rw [o]
    rw [hx]
    norm_num