import Mathlib


open Polynomial


lemma lemma_1 {s p : ℝ} (h1 : p^2 * (s + 1) + s = 0) (h2 : p * (s^2 + s - p) = -1) :
    p^6 + p^4 + p^3 - p^2 - 1 = 0 := by
  have h3 : s = -p^2 / (p^2 + 1) := by
    have h4 : p^2 + 1 ≠ 0 := by
      nlinarith [sq_nonneg p]
    field_simp
    nlinarith
  have h4 : p * (s^2 + s - p) = -1 := h2
  rw [h3] at h4
  have h5 : p^2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg p]
  field_simp [h5] at h4
  nlinarith [sq_nonneg (p^2), sq_nonneg (p + 1), sq_nonneg (p - 1), sq_pos_of_ne_zero (show (p^2 + 1 : ℝ) ≠ 0 by nlinarith [sq_nonneg p] ) ]


theorem algebra_139531 {x1 x2 : ℝ} (hx1 : x1^4 + x1^3 - 1 = 0) (hx2 : x2^4 + x2^3 - 1 = 0)
    (hx12 : x1 ≠ x2) : (x1 * x2)^6 + (x1 * x2)^4 + (x1 * x2)^3 - (x1 * x2)^2 - 1 = 0 := by
  have h12 : x1^4 + x1^3 - 1 = 0 := hx1
  have h22 : x2^4 + x2^3 - 1 = 0 := hx2
  have h32 : (x1^4 - x2^4) + (x1^3 - x2^3) = 0 := by
    nlinarith
  -- Factor the difference.
  have h42 : (x1 - x2) * ((x1 + x2) * (x1^2 + x2^2) + (x1^2 + x1 * x2 + x2^2)) = 0 := by
    ring_nf at h32 ⊢
    nlinarith

  -- Since $x1 \neq x2$, we have $x1 - x2 \neq 0$. Therefore, the factor must be zero.
  have h52 : (x1 + x2) * (x1^2 + x2^2) + (x1^2 + x1 * x2 + x2^2) = 0 := by
    apply (mul_left_inj' (show x1 - x2 ≠ 0 by
      intro h
      apply hx12
      linarith
    )).mp
    linarith

  have h62 : (x1 * x2)^2 * (x1 + x2 + 1) + (x1 + x2) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by 
      intro h
      apply hx12
      linarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (x1^2 - x2^2), sq_nonneg (x1^2 + x2^2), sq_nonneg (x1*x2)]

  have h72 : (x1 * x2) * ((x1 + x2)^2 + (x1 + x2) - (x1 * x2)) = -1 := by
    nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by 
      intro h
      apply hx12
      linarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (x1^2 - x2^2), sq_nonneg (x1^2 + x2^2), sq_nonneg (x1*x2)]

  -- Now apply lemma_1 with $p = x1*x2$ and $s = x1+x2$.
  have h82 : (x1 * x2)^6 + (x1 * x2)^4 + (x1 * x2)^3 - (x1 * x2)^2 - 1 = 0 := by
    apply lemma_1 (s := x1 + x2) (p := x1 * x2) 
    all_goals
      nlinarith [h62, h72]

  exact h82