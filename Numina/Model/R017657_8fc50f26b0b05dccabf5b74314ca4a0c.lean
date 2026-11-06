import Mathlib

theorem algebra_50087 {a b : ℝ} (ha : ∃ m : ℤ, a = m) (h : 2 * a + a ^ 2 = 2 * b + b ^ 2) :
    ∃ n : ℤ, b = n := by
  rcases ha with ⟨m, ha⟩
  have h1 : (a - b) * (a + b + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case $a - b = 0$, so $b = a$
    have hb : b = a := by
      linarith
    refine ⟨m, by simp [hb, ha]⟩
  · -- Case $a + b + 2 = 0$, so $b = -a - 2$
    have hb : b = -a - 2 := by
      linarith
    refine ⟨-(m : ℤ) - 2, by
      simp [hb, ha]
      <;> ring_nf <;> norm_num
    ⟩