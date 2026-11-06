import Mathlib

theorem algebra_97821 {a b x : ℝ} (ha : a ≠ b) (h : a^3 - b^3 = 19 * x^3) (h1 : a - b = x) :
    a = 3 * x ∨ a = -2 * x := by

  have h2 : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by 
    ring
  rw [h2] at h
  rw [h1] at h

  have h2 : x * (a^2 + a * b + b^2) = 19 * x^3 := by
    linarith
  
  have hx : x ≠ 0 := by
    by_contra hz
    have hz1 : a - b = 0 := by
      linarith [h1, hz]
  
    have hz2 : a = b := by linarith
  
    contradiction
  
  have h3 : a^2 + a * b + b^2 = 19 * x^2 := by
    apply (mul_left_inj' hx).mp
    linarith
  
  have h4 : a = b + x := by linarith
  
  rw [show a = b + x by linarith] at h3
  
  have h5 : 3 * b^2 + 3 * b * x - 18 * x^2 = 0 := by
    nlinarith
  
  have h6 : (b - 2 * x) * (b + 3 * x) = 0 := by
    nlinarith
  
  cases (mul_eq_zero.mp h6) with
  | inl h7 =>
  
    have hb : b = 2 * x := by linarith
  
    have ha : a = 3 * x := by 
      linarith [hb, h1]
  
    left
    linarith [ha]
  
  | inr h8 =>
  
    have hb : b = -3 * x := by linarith
  
    have ha : a = -2 * x := by 
      nlinarith [hb, h1]
  
    right
    linarith [ha]