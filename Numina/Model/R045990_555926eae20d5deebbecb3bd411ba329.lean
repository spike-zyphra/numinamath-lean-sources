import Mathlib

open Real
open scoped BigOperators

theorem inequalities_246919 (a b c A B C : ℝ)
  (h_pos_a : 0 < a) (h_pos_b : 0 < b) (h_pos_c : 0 < c)
  (h_angles : A + B + C = π)
  (h_pos_A : 0 < A) (h_pos_B : 0 < B) (h_pos_C : 0 < C)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) 
  (h_law_of_sines : a/sin A = b/sin B ∧ b/sin B = c/sin C)
  (h_law_of_cosines : a^2 = b^2 + c^2 - 2*b*c*cos A ∧     
                      b^2 = c^2 + a^2 - 2*c*a*cos B ∧ 
                      c^2 = a^2 + b^2 - 2*a*b*cos C) :
  a^3 * cos A + b^3 * cos B + c^3 * cos C ≤ (3 / 2) * a * b * c := by

  have hcos_A : cos A = (b^2 + c^2 - a^2) / (2 * b * c) := by
    have h₁ := h_law_of_cosines.left
    have : 2 * b * c * cos A = b^2 + c^2 - a^2 := by linarith
    field_simp [(show b ≠ 0 by linarith), (show c ≠ 0 by linarith)]
    linarith
  
  have hcos_B : cos B = (a^2 + c^2 - b^2) / (2 * a * c) := by
    have h₂ := h_law_of_cosines.right.left
    have : 2 * a * c * cos B = a^2 + c^2 - b^2 := by linarith
    field_simp [(show a ≠ 0 by linarith), (show c ≠ 0 by linarith)]
    linarith
  
  have hcos_C : cos C = (a^2 + b^2 - c^2) / (2 * a * b) := by
    have h₃ := h_law_of_cosines.right.right
    have : 2 * a * b * cos C = a^2 + b^2 - c^2 := by linarith
    field_simp [(show a ≠ 0 by linarith), (show b ≠ 0 by linarith)]
    linarith
  
  rw [hcos_A, hcos_B, hcos_C]

  have h2 : 0 < a * b * c := mul_pos (mul_pos h_pos_a h_pos_b) h_pos_c
  
  have h3 : a ^ 3 * ((b^2 + c^2 - a^2) / (2 * b * c)) + b ^ 3 * ((a^2 + c^2 - b^2) / (2 * a * c)) + c ^ 3 * ((a^2 + b^2 - c^2) / (2 * a * b)) - (3 / 2) * a * b * c ≤ 0 := by
  
    have h4 : a ^ 3 * ((b^2 + c^2 - a^2) / (2 * b * c)) + b ^ 3 * ((a^2 + c^2 - b^2) / (2 * a * c)) + c ^ 3 * ((a^2 + b^2 - c^2) / (2 * a * b)) - (3 / 2) * a * b * c = 
      (a ^ 4 * (b ^ 2 + c ^ 2 - a ^ 2) + b ^ 4 * (a ^ 2 + c ^ 2 - b ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2 - c ^ 2) - 3 * a ^ 2 * b ^ 2 * c ^ 2) / (2 * a * b * c) := by
      field_simp
      ring
  
    rw [h4]

    have h5 : a ^ 4 * (b ^ 2 + c ^ 2 - a ^ 2) + b ^ 4 * (a ^ 2 + c ^ 2 - b ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2 - c ^ 2) - 3 * a ^ 2 * b ^ 2 * c ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
        sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 + c ^ 2 - a ^ 2), sq_nonneg (c ^ 2 + a ^ 2 - b ^ 2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h_pos_a, h_pos_b, h_pos_c,
        mul_pos h_pos_a h_pos_b, mul_pos h_pos_b h_pos_c, mul_pos h_pos_c h_pos_a,
        mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < b ^ 2 by nlinarith), 
        mul_pos (show 0 < b ^ 2 by nlinarith) (show 0 < c ^ 2 by nlinarith), 
        mul_pos (show 0 < c ^ 2 by nlinarith) (show 0 < a ^ 2 by nlinarith)]
  
    have h6 : a ^ 4 * (b ^ 2 + c ^ 2 - a ^ 2) + b ^ 4 * (a ^ 2 + c ^ 2 - b ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2 - c ^ 2) - 3 * a ^ 2 * b ^ 2 * c ^ 2 ≤ 0 := by
      linarith
  
    have h7 : (a ^ 4 * (b ^ 2 + c ^ 2 - a ^ 2) + b ^ 4 * (a ^ 2 + c ^ 2 - b ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2 - c ^ 2) - 3 * a ^ 2 * b ^ 2 * c ^ 2) / (2 * a * b * c) ≤ 0 := by
  
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
  
      positivity
  
    linarith
  
  linarith [h3]
  all_goals try { linarith }