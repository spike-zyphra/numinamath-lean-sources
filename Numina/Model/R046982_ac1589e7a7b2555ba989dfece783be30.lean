import Mathlib

theorem algebra_186708 {x a b : ℝ} (ha : x ≠ a) (hb : x ≠ b) :
    (x - a) / (x - b) + (x - b) / (x - a) = 2.5 ↔
    x = 2 * a - b ∨ x = 2 * b - a := by 
  constructor 
  · -- Forward implication 
    intro h 
    have h1 : x - b ≠ 0 := by 
      intro h2 
      apply hb 
      linarith 
    have h2 : x - a ≠ 0 := by 
      intro h3 
      apply ha 
      linarith 
    have eq1 : (x - a) / (x - b) + (x - b) / (x - a) = 2.5 := h 
    field_simp [(show x - b ≠ 0 by exact h1), (show x - a ≠ 0 by exact h2)] at eq1 
    ring_nf at eq1 
    have h3 : (x - (2 * a - b)) * (x - (2 * b - a)) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h3) with h4 h5 
    · -- Case where x - (2 * a - b) = 0 
      left 
      linarith 
    · -- Case where x - (2 * b - a) = 0 
      right 
      linarith 
  · -- Backward implication 
    rintro (h | h)
    · -- Case x = 2 * a - b 
      rw [show x = 2 * a - b by linarith] 
      have h11 : (2 * a - b) - b ≠ 0 := by 
        by_contra h_eq 
        have h_eq1 : a = b := by 
          nlinarith 
        have h12 : x = a := by 
          nlinarith [h, h_eq1] 
        contradiction 
      have h12 : (2 * a - b) - a ≠ 0 := by 
        by_contra h_eq 
        have h_eq1 : a = b := by 
          nlinarith 
        have h13 : x = a := by 
          nlinarith [h, h_eq1] 
        contradiction 
      field_simp [(show (2 * a - b) - b ≠ 0 by exact h11), 
                  (show (2 * a - b) - a ≠ 0 by exact h12)]
      ring_nf 
      <;> norm_num 
    · -- Case x = 2 * b - a 
      rw [show x = 2 * b - a by linarith] 
      have h11 : (2 * b - a) - b ≠ 0 := by 
        by_contra h_eq 
        have h_eq1 : a = b := by 
          nlinarith 
        have h12 : x = b := by 
          nlinarith [h, h_eq1] 
        contradiction 
      have h12 : (2 * b - a) - a ≠ 0 := by 
        by_contra h_eq 
        have h_eq1 : a = b := by 
          nlinarith 
        have h13 : x = b := by 
          nlinarith [h, h_eq1] 
        contradiction 
      field_simp [(show (2 * b - a) - b ≠ 0 by exact h11), 
                  (show (2 * b - a) - a ≠ 0 by exact h12)]
      ring_nf 
      <;> norm_num