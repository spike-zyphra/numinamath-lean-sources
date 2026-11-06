import Mathlib

theorem number_theory_276721 (n : ℕ) :
    10 ∣ 3^n + 1 → 10 ∣ 3^(n + 4) + 1 := by
  intro h
  have h1 : 3 ^ (n + 4) + 1 = 81 * (3 ^ n) + 1 := by
    ring_nf
  rw [h1]
  -- Notice that we can write $81 \cdot 3^n + 1 = 80 \cdot 3^n + (3^n + 1)$.
  -- $80 \cdot 3^n$ is clearly divisible by 80, which is divisible by 10.
  -- And $3^n + 1$ is divisible by 10 by our hypothesis h.
  -- Therefore the total expression is divisible by 10.
  omega