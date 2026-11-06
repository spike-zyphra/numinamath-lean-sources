import Mathlib

-- What is the sum of the solutions to the equation x^4 = 12/(7-x^(1/4))?

theorem AIME_algebra_94869 (x : ℝ) (hx : x ≥ 0) (ne_zero : (7 - x ^ ((1 : ℝ) / 4)) ≠ 0) :
x ^ ((1 : ℝ) / 4) = 12 / (7 - x ^ ((1 : ℝ) / 4)) ↔ (x = 256) ∨ (x = 81) := by
  constructor
  -- We rewrite the equation
  · intro h
    ring_nf at h
    rw [mul_comm, eq_mul_inv_iff_mul_eq₀ ne_zero, ← sub_eq_zero] at h
    have : (x ^ ((1 : ℝ) / 4) - 3) * (x ^ ((1 : ℝ) / 4) - 4) = 0 := by
      rw [← neg_eq_zero, ← h]
      ring
    rw [mul_eq_zero] at this
    rcases this with (h | h)
    -- If the first factor is zero, then x = 81
    · rw [sub_eq_zero] at h
      apply Or.inr
      rw [(by norm_num : ((81 : ℝ) = 3^(4 : ℝ))), ← h]
      rw [one_div, Real.rpow_inv_rpow]
      assumption
      linarith
    -- If the second factor is zero, then x = 256
    · rw [sub_eq_zero] at h
      apply Or.inl
      rw [(by norm_num : ((256 : ℝ) = 4^(4 : ℝ)))]
      nth_rewrite 1 [← h]
      rw [one_div, Real.rpow_inv_rpow]
      assumption
      linarith
    -- We show that x=81 and x=256 are solutions
  · intro h
    rcases h with (h | h)
    · rw [h, (by norm_num : (256 : ℝ) = 4^(4 : ℝ))]
      simp only [one_div, Nat.ofNat_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        Real.rpow_rpow_inv]
      norm_num
    · rw [h, (by norm_num : (81 : ℝ) = 3^(4 : ℝ))]
      simp only [one_div, Nat.ofNat_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        Real.rpow_rpow_inv]
      norm_num