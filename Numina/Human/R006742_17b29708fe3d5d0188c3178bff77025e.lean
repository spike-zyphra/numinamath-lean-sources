import Mathlib

/-Let $a$ be a natural number whose last digit is $7$.
Let $N$ be a natural number such that $N \equiv 3 \pmod 4$. Determine the last digit of $a^N+5$.
Show the answer is $8$.-/

theorem number_theory_640714 (N a: ℕ) (h1: a % 10 = 7) (h2: N % 4 = 3): (a ^ N + 5) % 10 = 8 := by
  rw [Nat.add_mod]
  suffices a ^ N % 10 = 3 by
    simp [this]
  rw [Nat.pow_mod]
  rw [h1]
  clear h1
  replace h2: (N + 1) % 4 = 0 := by
    simp [Nat.add_mod, h2]
  apply Nat.dvd_of_mod_eq_zero at h2
  apply exists_eq_mul_right_of_dvd at h2
  obtain ⟨k, hk⟩ := h2
  set s:= k - 1
  replace hk: N = 4 * s + 3 := by omega
  rw [hk]
  clear hk
  ring_nf
  rw [Nat.mul_mod]
  rw [show 343 % 10 = 3 by norm_num]
  suffices 7 ^ (s * 4) % 10 = 1 by simp [this]
  rw [show s * 4 = 4 * s by ring]
  simp [Nat.pow_mul,Nat.pow_mod]
