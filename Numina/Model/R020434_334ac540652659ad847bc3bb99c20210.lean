import Mathlib

theorem algebra_204772 (x y : ℝ) :
    5 * Real.cos y ^ 2 + x ^ 2 - 2 * x * Real.cos y - 8 * x + 20 = 0 ↔
    ∃ n : ℤ, x = 5 ∧ y = 2 * n * Real.pi := by
  constructor
  · -- Assume the equation holds, prove the existence of $n$
    intro h
    have h1 : (x - Real.cos y - 4) ^ 2 + 4 * (Real.cos y - 1) ^ 2 = 0 := by
      nlinarith [Real.cos_sq_add_sin_sq y, sq_nonneg (x - Real.cos y - 4), sq_nonneg (Real.cos y - 1)]
    have h2 : (x - Real.cos y - 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - Real.cos y - 4), sq_nonneg (Real.cos y - 1)]
    have h3 : Real.cos y - 1 = 0 := by
      nlinarith [sq_nonneg (x - Real.cos y - 4), sq_nonneg (Real.cos y - 1)]
    have hc : Real.cos y = 1 := by linarith
    have h4 : x = 5 := by
      nlinarith [hc, Real.sin_sq_add_cos_sq y]
    have h5 : ∃ n : ℤ, y = 2 * n * Real.pi := by
      rw [Real.cos_eq_one_iff] at hc
      rcases hc with ⟨n, hn⟩
      use n
      all_goals linarith
    rcases h5 with ⟨n, hn⟩
    exact ⟨n, by linarith [h4], hn⟩
  · -- Assume the existence of $n$, prove the equation holds
    rintro ⟨n, hx, hy⟩
    have hc : Real.cos y = 1 := by
      rw [show y = 2 * n * Real.pi by linarith [hy]]
      have h2 : Real.cos (2 * n * Real.pi) = 1 := by
        have h4 : Real.cos (2 * n * Real.pi) = 1 := by
          have h1 : 2 * n * Real.pi = (n : ℝ) * (2 * Real.pi) := by ring
          rw [h1]
          have h2 : Real.cos (n * (2 * Real.pi)) = 1 := by
            exact Real.cos_int_mul_two_pi n
          nlinarith
        nlinarith
      nlinarith
    rw [hx, hc]
    nlinarith [Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq y]