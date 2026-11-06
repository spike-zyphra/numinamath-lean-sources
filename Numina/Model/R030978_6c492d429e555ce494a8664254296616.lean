import Mathlib

theorem algebra_140918 (a n : ℕ) (ha : a > 0) : a ^ n + a ^ n = a ^ (n + 1) ↔ a = 2 := by
  constructor
  · -- Assume $a^n + a^n = a^{n+1}$, we need to show $a = 2$.
    intro h
    have eq1 : a ^ n + a ^ n = 2 * (a ^ n) := by
      ring
    rw [eq1] at h
    have eq2 : a ^ (n + 1) = a ^ n * a := by
      ring_nf
    rw [eq2] at h
    have h1 : a ^ n > 0 := by
      apply Nat.pow_pos
      linarith
    have h2 : 2 = a := by
      nlinarith [h, h1]
    omega
  · -- Assume $a = 2$, we need to show $a^n + a^n = a^{n+1}$.
    intro h
    rw [h]
    have eq1 : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
      ring_nf
    exact eq1