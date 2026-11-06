import Mathlib

theorem algebra_300907 (a b c d : ℝ) (h₀ : a ≠ b) (h₁ : c ≠ d)
    (h₂ : a^2 + a * c = 2) (h₃ : b^2 + b * c = 2) (h₄ : c^2 + a * c = 4)
    (h₅ : d^2 + a * d = 4) : 6 * a + 2 * b + 3 * c + 2 * d = 0 := by
  have eq1 : a + b + c = 0 := by
    have h6 : a^2 + a * c - (b^2 + b * c) = 0 := by linarith
    have h7 : a^2 - b^2 + (a * c - b * c) = 0 := by linarith [h6]
    have h8 : (a - b) * (a + b + c) = 0 := by
      ring_nf at h7 ⊢
      linarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- case a - b = 0, so a = b, contradict h₀
      exfalso
      apply h₀
      linarith
    · -- case a + b + c = 0
      linarith

  have eq2 : a + c + d = 0 := by
    have h8 : c^2 + a * c - (d^2 + a * d) = 0 := by linarith
    have h9 : c^2 - d^2 + (a * c - a * d) = 0 := by linarith [h8]
    have h10 : (c - d) * (c + d + a) = 0 := by 
      ring_nf at h9 ⊢
      linarith
    cases' (mul_eq_zero.1 h10) with h11 h12
    · -- case c - d = 0, so c = d, contradict h₁
      exfalso
      apply h₁
      linarith
    · -- case c + d + a = 0
      linarith

  have eq3 : b = d := by
    nlinarith [eq1, eq2]

  have eq4 : c = -a - b := by
    linarith [eq1]

  have eq8 : 6 * a + 2 * b + 3 * c + 2 * d = 3 * a + b := by
    rw [show d = b by linarith [eq3]]
    rw [show c = -a - b by linarith [eq4]]
    linarith

  have eq6 : a * b = -2 := by 
    rw [eq4] at h₂
    nlinarith

  have eq9 : b ^ 2 = 6 := by
    have eq7 : d = b := by
      linarith [eq3]
    rw [eq7] at h₅
    nlinarith [eq6]

  have eq10 : (3 * a + b) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a), sq_nonneg (b), eq6, eq9]

  have eq11 : 3 * a + b = 0 := by 
    nlinarith [eq10]

  linarith [eq8, eq11]