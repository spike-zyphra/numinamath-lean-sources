import Mathlib

theorem algebra_8113 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = 0) :
    1 / ((b ^ 2 + c ^ 2 - a ^ 2)) + 1 / ((c ^ 2 + a ^ 2 - b ^ 2)) +
    1 / ((a ^ 2 + b ^ 2 - c ^ 2)) = 0 := by
  have ha2 : a = -b - c := by linarith 
  have eq1 : b ^ 2 + c ^ 2 - a ^ 2 = -2 * b * c := by 
    rw [ha2]
    ring
  have eq2a : c ^ 2 + a ^ 2 - b ^ 2 = 2 * c * (b + c) := by 
    rw [ha2]
    ring
  have eq2b : a ^ 2 + b ^ 2 - c ^ 2 = 2 * b * (b + c) := by 
    rw [ha2]
    ring 
  rw [eq1, eq2a, eq2b]
  have h1 : b + c ≠ 0 := by 
    by_contra h1
    have h2 : a = 0 := by linarith [h, h1]
    contradiction 
  field_simp [(show b ≠ 0 by exact hb), (show c ≠ 0 by exact hc), 
      (show b + c ≠ 0 by 
          by_contra h1
          have h2 : a = 0 := by linarith [h, h1]
          contradiction 
      ), 
      (show b * c ≠ 0 by 
          apply mul_ne_zero 
          exact hb 
          exact hc 
      ), 
      (show c * (b + c) ≠ 0 by 
          apply mul_ne_zero 
          exact hc 
          by_contra h1 
          have h2 : b + c = 0 := by 
            simpa using h1 
          have h1' : b + c = 0 := h2 
          have h1'' : a = 0 := by linarith [h, h1']
          contradiction 
      ), 
      (show b * (b + c) ≠ 0 by 
          apply mul_ne_zero 
          exact hb 
          by_contra h1 
          have h2 : b + c = 0 := by 
            simpa using h1 
          have h1' : b + c = 0 := h2 
          have h1'' : a = 0 := by linarith [h, h1']
          contradiction 
      )
  ]
  <;> ring_nf 
  <;> nlinarith