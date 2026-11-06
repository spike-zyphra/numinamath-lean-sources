import Mathlib

theorem algebra_14563 {x : ℝ} (hx : x > 0) (h : √x ^ 3 = 64) : x = 16 := by
  have h1 : Real.sqrt x ^ 3 = 64 := h
  have h2 : Real.sqrt x = 4 := by
    have h6 : Real.sqrt x ^ 3 - 64 = 0 := by linarith
    have h7 : Real.sqrt x ^ 2 + 4 * Real.sqrt x + 16 > 0 := by
      nlinarith [sq_nonneg (Real.sqrt x + 2)]
    have h8 : (Real.sqrt x - 4) * (Real.sqrt x ^ 2 + 4 * Real.sqrt x + 16) = 0 := by
      ring_nf at h6 ⊢
      linarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case Real.sqrt x - 4 = 0:
      linarith
    · -- Case Real.sqrt x ^ 2 + 4 * Real.sqrt x + 16 = 0:
      nlinarith [show Real.sqrt x ^ 2 + 4 * Real.sqrt x + 16 > 0 by
        nlinarith [sq_nonneg (Real.sqrt x + 2)]
      ]
  have h5 : x = 16 := by
    have h6 : Real.sqrt x = 4 := h2
    have h7 : (Real.sqrt x) ^ 2 = x := by
      rw [Real.sq_sqrt]
      linarith
    rw [h6] at h7
    nlinarith [Real.sqrt_nonneg x]
  exact h5