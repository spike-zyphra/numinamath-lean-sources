import Mathlib

theorem algebra_161458 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a + b = 1) :
    a / (b^3 - 1) - b / (a^3 - 1) = 2 * (b - a) / (a^2 * b^2 + 3) := by
  have hb_eq : b = 1 - a := by 
    linarith
  rw [hb_eq]
  have h1 : a ≠ 0 := ha
  have h2 : (1 - a) ≠ 0 := by
    intro h0
    apply hb
    linarith
  have h3 : (1 - a) ^ 3 - 1 ≠ 0 := by
    have h4 : (1 - a) ^ 3 - 1 = -a * (a ^ 2 - 3 * a + 3) := by
      ring_nf
    rw [h4]
    intro h0
    have h5 : a * (a ^ 2 - 3 * a + 3) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- case h6 = a = 0 
      exfalso 
      apply ha 
      linarith 
    · -- h7 : a^2 - 3 * a + 3 = 0 
      have h8 : a^2 - 3 * a + 3 = 0 := h7 
      nlinarith [sq_nonneg (a - 3 / 2)]
  
  have h4 : a ^ 3 - 1 ≠ 0 := by
    by_contra h0 
    have h5 : a^3 = 1 := by linarith 
    have h6 : a = 1 := by
      have h7 : a^3 - 1 = 0 := by linarith
      have h8 : a^3 - 1 = (a - 1) * (a^2 + a + 1) := by ring
      rw [h8] at h7 
      cases' (mul_eq_zero.mp h7) with h9 h10 
      · -- h9 : a - 1 = 0 
        linarith 
      · -- h10 : a^2 + a + 1 = 0 
        nlinarith [sq_nonneg (a + 1 / 2) ]
    have h7 : (1 - a) = 0 := by
      linarith 
    contradiction
  
  have h4' : a^2 * (1 - a) ^ 2 + 3 ≠ 0 := by
    have h5 : a^2 * (1 - a) ^ 2 ≥ 0 := by 
      positivity 
    nlinarith [ sq_pos_of_ne_zero ha, sq_nonneg (1 - a) ]

  field_simp [(show (1 - a) ^ 3 - 1 ≠ 0 by simpa using h3), (show a ^ 3 - 1 ≠ 0 by simpa using h4), (show a^2 * (1 - a) ^ 2 + 3 ≠ 0 by simpa using h4')]
  <;> ring_nf <;> nlinarith [ sq_nonneg (a^2 * (1 - a) ^ 2 ), sq_nonneg (a - (1 - a) ), sq_nonneg (a + (1 - a) - 1 ), sq_nonneg (a^2 - (1 - a)^2 ), sq_nonneg (a * (1 - a) ), sq_nonneg (a + (1 - a) ) ]