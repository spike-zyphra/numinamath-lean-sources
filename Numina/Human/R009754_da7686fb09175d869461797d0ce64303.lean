import Mathlib

/- If the two roots of the quadratic $4x^2+7x+k$ are $\frac{-7\pm i\sqrt{15}}{8}$, what is $k$? -/
theorem algebra_20382 (k : ℝ) (h : ∃ x1 x2 : ℂ, x1 ≠ x2 ∧ 4 * x1 ^ 2 + 7 * x1 + k = 0 ∧ 4 * x2 ^ 2 + 7 * x2 + k = 0 ∧ x1 = -7 / 8 + Real.sqrt 15 / 8 * Complex.I ∧ x2 = -7 / 8 - Real.sqrt 15 / 8 * Complex.I) :
    k = 4 := by
  obtain ⟨x1, x2, ⟨_, h₁, _, h₃, h₄⟩⟩ := h
  -- By Vieta's formula, it suffices to show that h / 4 is the product of the two roots. 
  suffices h : k = 4 * x1 * x2 by
    rw [h₃, h₄] at h
    ring_nf at h
    norm_cast at h
    rw [Complex.I_sq, Real.sq_sqrt] at h
    rify at h
    norm_num at h
    norm_cast at h
    norm_num
  calc
    k = x1 * (-7 - 4 * x1) := (eq_neg_of_add_eq_zero_right h₁).trans (by field_simp; ring_nf)
    _ = x1 * (4 * x2) := by simp [show x1 ≠ 0 by rw [h₃]; by_contra!; rw [show (-7 / 8 : ℂ) = (-7 / 8 : ℝ) by norm_cast, show (Real.sqrt 15 : ℂ) / 8 = (Real.sqrt 15 / 8 : ℝ) by norm_cast, <-Complex.mk_eq_add_mul_I, <-Complex.eta 0] at this; injection this with h₅ h₆; norm_num at h₅]; rw [h₃, h₄]; ring_nf
    _ = 4 * x1 * x2 := by ac_rfl
