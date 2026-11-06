import Mathlib

theorem number_theory_22698 {b : ℤ} (hb : b > 1) :
  (1*b+3) * (1*b+5) = (2*b^2+4*b+3) ↔ b = 6 := by
  constructor
  · -- Assume (1 * b + 3) * (1 * b + 5) = (2 * b ^ 2 + 4 * b + 3), prove b = 6
    intro h
    have eq1 : (1 * b + 3) * (1 * b + 5) = b^2 + 8 * b + 15 := by
      ring
    rw [eq1] at h
    have h1 : b ^ 2 - 4 * b - 12 = 0 := by
      nlinarith
    have h2 : (b - 6) * (b + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- case $b - 6 = 0$, so $b = 6$.
      linarith
    · -- case $b + 2 = 0$, so $b = -2$.
      have hb1 : b = -2 := by linarith
      nlinarith
  · -- Assume b = 6, prove (1 * b + 3) * (1 * b + 5) = (2 * b ^ 2 + 4 * b + 3)
    intro h
    rw [h]
    norm_num