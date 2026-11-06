import Mathlib

theorem algebra_207760 (a d : ℝ) (h₀ : a > a - d) (h₁ : a - d > a - 2 * d)
    (h₂ : a - 2 * d > a - 3 * d) (h₃ : a - 3 * d > a - 4 * d) (h₄ : a^3 + (a - d)^3 + (a - 2 * d)^3 + (a - 3 * d)^3 + (a - 4 * d)^3 = 0)
    (h₅ : a^4 + (a - d)^4 + (a - 2 * d)^4 + (a - 3 * d)^4 + (a - 4 * d)^4 = 306) :
    a - 4 * d = -2 * Real.sqrt 3 := by
  have ha1 : d > 0 := by
    nlinarith 
  have eq1 : 5 * a^3 - 30 * a^2 * d + 90 * a * d^2 - 100 * d^3 = 0 := by
    ring_nf at h₄
    nlinarith
  have eq3 : a = 2 * d := by 
    have h6 : a^3 - 6 * a^2 * d + 18 * a * d^2 - 20 * d^3 = 0 := by
      nlinarith [eq1]
    have h7 : (a - 2 * d) * (a^2 - 4 * d * a + 10 * d^2) = 0 := by 
      nlinarith [h6]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- a - 2d = 0 
      linarith 
    · -- a^2 -4da +10d^2=0
      have h10 : a^2 - 4 * d * a + 10 * d^2 = 0 := by
        linarith [h9]
      have h11 : (a - 2 * d) ^ 2 + 6 * d^2 = 0 := by 
        nlinarith 
      have h12 : (a - 2 * d) ^ 2 ≥ 0 := by
        apply sq_nonneg 
      have h13 : 6 * d^2 > 0 := by
        nlinarith [show d ^ 2 > 0 by nlinarith] 
      have h14 : (a - 2 * d) ^ 2 = 0 := by 
        nlinarith 
      have h15 : d^2 = 0 := by 
        nlinarith 
      have h16 : d = 0 := by 
        nlinarith 
      linarith 
  have eq2 : 34 * (d^4) = 306 := by 
    rw [show a = 2 * d by linarith [eq3]] at h₅
    ring_nf at h₅
    nlinarith
  have eq6 : d^2 = 3 := by 
    nlinarith [sq_nonneg (d^2 - 3)]
  have eq7 : d = Real.sqrt 3 := by 
    have h8 : d ^ 2 = 3 := eq6 
    have h9 : d > 0 := ha1
    have h10 : d = Real.sqrt 3 := by
      rw [← h8]
      field_simp 
    exact h10 
  have eq9 : a - 4 * d = -2 * Real.sqrt 3 := by
    have h8 : d = Real.sqrt 3 := eq7 
    have eq8 : a = 2 * d := eq3 
    linarith [eq8, h8] 
  exact_mod_cast eq9