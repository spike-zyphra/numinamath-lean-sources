import Mathlib

theorem algebra_177753 {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c ≠ 0) (h1 : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    a = -b ∨ b = -c ∨ a = -c := by

  have h_eq : (a + b) * (b + c) * (c + a) = 0 := by
    have eq1 : b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) = a * b * c := by
      have eq44 : (1 / a + 1 / b + 1 / c) = (1 / (a + b + c)) := by linarith [h1]
      have h_eq3 : (b * c + a * c + a * b) * (a + b + c) = a * b * c := by
        have eq55 : (1 / a + 1 / b + 1 / c) * (a * b * c * (a + b + c)) = a * b * c := by
          have h_eq5 : (1 / a + 1 / b + 1 / c) = (1 / (a + b + c)) := by linarith [h1]
          rw [h_eq5]
          field_simp [show a + b + c ≠ 0 by exact h, ha, hb, hc] 
        have eq66 : (1 / a + 1 / b + 1 / c) * (a * b * c * (a + b + c)) = (b * c + a * c + a * b) * (a + b + c) := by
          field_simp [ha, hb, hc]
          <;> ring_nf
        linarith [eq55, eq66]
      have : b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) = (b * c + a * c + a * b) * (a + b + c) := by 
        ring
      linarith [this, h_eq3]
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show c ≠ 0 by exact hc)]
  
  cases' (mul_eq_zero.mp h_eq) with h2 h3
  cases' (mul_eq_zero.mp h2) with h4 h5
  · -- First case: a + b = 0, which implies a = -b
    left
    linarith
  · -- Second case: b + c = 0, which implies b = -c
    right
    left
    linarith
  · -- Third case: c + a = 0, which implies a = -c
    right
    right
    linarith