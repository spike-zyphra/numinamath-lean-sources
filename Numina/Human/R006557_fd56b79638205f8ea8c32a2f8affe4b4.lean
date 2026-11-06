import Mathlib

/-Let $X$ and $Y$ be positive integers. Suppose $a$ and $b$ are digits (integers from 0 to 9 inclusive).

The number $N = X \cdot 10^4 + 1000a + 100b + Y$ is constructed.

If $N$ is a multiple of 99, these conditions may determine $a$ and $b$.

Let $X=11$ and $Y=22$. Show that if $N$ is a multiple of 99, then $a+b=12$.-/

theorem number_theory_638461 (X Y a b N: ℤ) (ha: 0 ≤ a ∧ a ≤ 9) (hb: 0 ≤ b ∧ b ≤ 9)
  (hN: N = X * 10^4 + a * 1000 + b * 100 + Y) (hX: X = 11) (hY: Y = 22) (h: 99 ∣ N): a + b = 12 := by

  simp [hN, hX, hY] at h
  clear hN hX hY
  replace h: 99 ∣ 33 + 10 * a + b := by
    rw [show 33 + 10 * a + b = (110000 + a * 1000 + b * 100 + 22) - (99 * (1111 + a * 10 + b)) by omega]
    apply dvd_sub
    .
      tauto
    .
      simp
  apply exists_eq_mul_right_of_dvd at h
  obtain ⟨k, hk⟩ := h
  have lk: k < 2 := by omega
  have rk: 0 < k := by omega
  have vk: k = 1 := by
    omega
  simp [vk] at hk
  omega

