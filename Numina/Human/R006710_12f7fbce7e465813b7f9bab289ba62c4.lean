import Mathlib

/- Let m be an odd positive integer. Prove that
3 ^ 6m + 2 ^ 6m is divisible by 13 -/

theorem number_theory_640361 (m: ℕ) (h: Odd m): 13 ∣ 3 ^ (6 * m) + 2 ^ (6 * m) := by
  apply Odd.exists_bit1 at h
  obtain ⟨k, rfl⟩ := h
  rw [show 6 * (2 * k + 1) = 12 * k + 6 by omega]
  ring_nf
  have s: 2 ^ (k * 12) = (2 ^ 12) ^ k := by
    rw [show k * 12 = 12 * k by ring]
    rw [Nat.pow_mul]
  have t: 3 ^ (k * 12) = (3 ^ 12) ^ k := by
    rw [show k * 12 = 12 * k by ring]
    rw [Nat.pow_mul]
  rw [s, t]
  clear s t
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod]
  suffices (2 ^ 12) ^ k * 64 % 13 = 12 ∧ (3 ^ 12) ^ k * 729 % 13 = 1 by
    rcases this with ⟨l, r⟩
    rw [l, r]
    simp
  constructor
  .
    rw [Nat.mul_mod]
    rw [Nat.pow_mod]
    rw [show 2 ^ 12 % 13 = 1 by simp]
    simp
  .
    rw [Nat.mul_mod]
    rw [Nat.pow_mod]
    rw [show 3 ^ 12 % 13 = 1 by simp]
    simp