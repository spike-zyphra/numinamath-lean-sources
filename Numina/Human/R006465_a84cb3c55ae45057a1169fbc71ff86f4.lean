import Mathlib

/-Let $b$ be a positive integer such that $b \equiv 2 \pmod 4$.
Determine the last digit of the number $2012^3 + 3^b$. Show the answer is 7.-/

theorem number_theory_637374 (b: ℕ) (h: b % 4 = 2): (2012 ^ 3 + 3 ^ b) % 10 = 7 := by

  replace h: (b + 2) % 4 = 0 := by
    rw [Nat.add_mod]
    simp [h]
  apply Nat.dvd_of_mod_eq_zero at h
  obtain ⟨s, h⟩ := h
  set t:= s - 1
  replace h: b = 4 * t + 2 := by
    omega
  clear_value t
  rw [Nat.add_mod]
  rw [show 2012 ^ 3 % 10 = 8 by rw [Nat.pow_mod]]
  suffices 3 ^ b % 10 = 9 by
    rw [this]
  rw [h]
  ring_nf
  rw [Nat.mul_mod]
  suffices 3 ^ (t * 4) % 10 = 1 by
    simp [this]
  rw [show t * 4 = 4 * t by ring]
  rw [Nat.pow_mul]
  simp
  rw [Nat.pow_mod]
  simp