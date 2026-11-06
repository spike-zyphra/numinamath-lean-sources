import Mathlib

/-Let $M$ be a positive integer such that $M \equiv 5 \pmod{14}$.
Prove that the number $(2M)^{5M} + (5M)^{2M}$ is divisible by 7.-/

theorem number_theory_636792 (M: ℕ) (h: M % 14 = 5): 7 ∣ (2 * M) ^ (5 * M) + (5 * M) ^ (2 * M) := by

  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod]
  have s1: (2 * M) ^ (5 * M) % 7 = 3 ^ (5 * M) % 7 := by
    have d: M % 7 = 5 := by
      rw [show M % 7 = M % 14 % 7 by omega]
      simp [h]
    rw [Nat.pow_mod]
    replace d: 2 * M % 7 = 3 := by
      rw [Nat.mul_mod]
      simp [d]
    simp [d]
  have s2: (5 * M) ^ (2 * M) % 7 = 4 ^ (2 * M) % 7 := by
    have d: M % 7 = 5 := by
      rw [show M % 7 = M % 14 % 7 by omega]
      simp [h]
    rw [Nat.pow_mod]
    replace d: 5 * M % 7 = 4 := by
      rw [Nat.mul_mod]
      simp [d]
    simp [d]
  simp [s1, s2]
  clear s1 s2
  have k1: 3 ^ (5 * M) % 7 = 5 ^ M % 7 := by
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
  have k2: 4 ^ (2 * M) % 7 = 2 ^ M % 7 := by
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
  rw [Nat.add_mod]
  simp [k1, k2]
  clear k1 k2
  replace h: M % 2 = 1 := by
    rw [show M % 2 = M % 14 % 2 by omega]
    simp [h]
  replace h: (M + 1) % 2 = 0 := by
    rw [Nat.add_mod]
    simp [h]
  apply Nat.dvd_of_mod_eq_zero at h
  apply exists_eq_mul_right_of_dvd at h
  obtain ⟨k, hk⟩ := h
  have u: 0 < k := by omega
  set s:= k - 1
  have h: M = 2 * s + 1 := by omega
  rw [h]
  clear hk u h
  ring_nf
  rw [show 2 ^ (s * 2) = 4 ^ s by rw [show s * 2 = 2 * s by omega]; rw [Nat.pow_mul]]
  rw [show 5 ^ (s * 2) = 25 ^ s by rw [show s * 2 = 2 * s by omega]; rw [Nat.pow_mul]]
  rw [Nat.add_mod]
  have u:  25 ^ s * 5 % 7 = 4 ^ s * 5 % 7 := by
    rw [Nat.mul_mod]
    rw [Nat.pow_mod]
    simp
  simp [u]
  clear u
  rw [show 4 ^ s * 2 + 4 ^ s * 5 = 4 ^ s * 7 by ring]
  simp