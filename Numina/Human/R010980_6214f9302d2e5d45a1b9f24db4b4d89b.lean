import Mathlib
open Real Set

/-Given that $x$ is a positive real, find the maximum possible value of

$$
\sin \left(\tan ^{-1}\left(\frac{x}{9}\right)-\tan ^{-1}\left(\frac{x}{16}\right)\right)
$$-/
theorem algebra_609823 : IsGreatest {y : ℝ | ∃ x : ℝ, 0 < x ∧ y = sin (arctan (x / 9) - arctan (x / 16))} (7 / 25) := by
  constructor
  · -- When x = 12, the value is 7/25
    simp only [mem_setOf_eq]
    use 12
    field_simp [Nat.ofNat_pos, true_and, sin_sub, sin_arctan, cos_arctan]
    rw [show (9 ^ 2 + 12 ^ 2 : ℝ) = 15 ^ 2 by norm_num, show (16 ^ 2 + 12 ^ 2 : ℝ) = 20 ^ 2 by norm_num]
    simp only [Nat.ofNat_nonneg, sqrt_sq]
    ring_nf
  · rintro _ ⟨x, hx₁, rfl⟩
    field_simp [sin_sub, sin_arctan, cos_arctan, div_le_div_iff₀]
    suffices 25 * x ≤ √(9 ^ 2 + x ^ 2) * √(16 ^ 2 + x ^ 2) by linarith
    rw [←sqrt_mul (by positivity), le_sqrt (by positivity) (by positivity)]
    linarith [sq_nonneg (x^2 - 144)]
