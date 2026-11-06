import Mathlib

theorem algebra_195627 {a b c d q : ℝ} (ha : a ≠ 0) (hq : q ≠ 0) (h : b = a * q) (h' : c = b * q) (h'' : d = c * q) (h''' : a * x^3 + b * x^2 + c * x + d = 0) :
    x = -q := by

  have hb : b = a * q := h
  have hc : c = a * q^2 := by
    rw [h']
    rw [hb]
    all_goals ring
  have hd : d = a * q^3 := by
    rw [h'']
    rw [hc]
    all_goals ring
  rw [hb, hc, hd] at h'''
  have eq1 : a * (x^3 + q * x^2 + q^2 * x + q^3) = 0 := by
    linarith
  have eq2 : x^3 + q * x^2 + q^2 * x + q^3 = 0 := by
    apply (mul_left_inj' ha).mp 
    linarith
  have eq3 : (x + q) * (x^2 + q^2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 eq3) with h1 h2
  · -- case where $x + q = 0$
    linarith 
  · -- case where $x^2 + q^2 = 0$
    have h4 : x^2 + q^2 = 0 := by 
      linarith
    have h5 : x^2 ≥ 0 := sq_nonneg x 
    have h6 : q^2 > 0 := by 
      apply sq_pos_of_ne_zero 
      exact hq 
    have h7 : x^2 + q^2 > 0 := by 
      nlinarith 
    linarith -- This apply linarith to h7 and h4, which contradicts