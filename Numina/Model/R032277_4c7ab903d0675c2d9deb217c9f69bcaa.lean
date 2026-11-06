import Mathlib

open Real Set
open scoped Real

theorem algebra_9077 (x : ℝ) :
  sin x ^ 2 - 2 * sin x = 0 ↔ ∃ k : ℤ, x = k * π := by
  constructor
  · -- Assume $\sin^2 x - 2 \sin x = 0$, prove $\exists k : \mathbb{Z}, x = k \cdot \pi$
    intro h
    have h1 : sin x * (sin x - 2) = 0 := by
      linarith
    cases' (mul_eq_zero.1 h1) with h2 h3
    · -- Case $\sin x = 0$
      obtain ⟨k, hk⟩ := sin_eq_zero_iff.1 h2
      exact ⟨k, by linarith⟩
    · -- Case $\sin x - 2 = 0$
      have h4 : sin x = 2 := by linarith
      have h5 : sin x ≤ 1 := by apply sin_le_one
      nlinarith
  · -- Assume $\exists k : \mathbb{Z}, x = k \cdot \pi$, prove $\sin^2 x - 2 \sin x = 0$
    rintro ⟨k, hk⟩
    have h1 : sin x = 0 := by
      rw [hk]
      have h1 : sin (k * π) = 0 := by
        have h5 : sin (k * π) = 0 := by
          have h6 : k * π = (k : ℝ) * π := by
            simp
          rw [h6]
          exact sin_int_mul_pi k
        exact h5
      exact h1
    rw [h1]
    all_goals norm_num