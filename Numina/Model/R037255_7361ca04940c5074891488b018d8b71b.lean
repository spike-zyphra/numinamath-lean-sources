import Mathlib

theorem algebra_10579 {a b : ℝ} {f f_inv : ℝ → ℝ} (hf : f = fun x => a * x + b)
    (hf_inv : f_inv = fun x => b * x + a) (h: ∀x, f (f_inv x) = x) : a + b = -2 := by

  have h1 := h 0
  simp [hf, hf_inv] at h1
  have h2 := h 1
  simp [hf, hf_inv] at h2
  have h3 : a ^ 2 + b = 0 := by
    nlinarith
  have h4 : a * b = 1 := by
    -- h2 is a * b + a ^ 2 + b = 1
    -- from h3: a^2 + b = 0, so b = -a^2
    -- be substituting into h2: a * (-a^2) + 0 = -a^3 = 1 - 0 = 1
    -- so a^3 = -1 
    -- but indeed we can get ab = 1 by:
    nlinarith [h3]
  -- Now we continue and solve for a and b
  have h5 : b = -a ^ 2 := by 
    nlinarith [h3]
  rw [h5] at h4
  have h6 : a ^ 3 = -1 := by 
    nlinarith [h4]
  have h7 : a = -1 := by
    have h8 : a ^ 3 + 1 = 0 := by
      linarith [h6]
    have h9 : (a + 1) * (a ^ 2 - a + 1) = 0 := by 
      ring_nf at h8 ⊢
      linarith
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- Case a + 1 = 0, so a = -1
      linarith 
    · -- Case a^2 - a + 1 = 0
      nlinarith [sq_nonneg (a - 1 / 2)]
  -- Now to find $b$ from $b = -a^2$
  have h8 : b = -1 := by
    rw [h7] at h5
    nlinarith
  linarith [h7, h8]