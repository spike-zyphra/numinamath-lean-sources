import Mathlib

theorem algebra_97236 {x a b : ℝ} (hx : x = a / b) (ha : a ≠ b) (hb : b ≠ 0) :
    (a + b) / (a - b) = (x + 1) / (x - 1) := by

  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith

  have h2 : x - 1 ≠ 0 := by 
    by_contra h3 
    have h31 : x = 1 := by linarith 
    have h4 : a / b = 1 := by 
      rw [show x = 1 by linarith [h31]] at hx 
      linarith
    -- From a / b = 1, we can multiply both sides by b (since b ≠ 0)
    -- to get a = b.
    have h5 : a = b := by 
      have h6 : a / b = 1 := h4 
      field_simp [hb] at h6 ⊢ 
      all_goals linarith 
    -- This contradicts the hypothesis `ha : a ≠ b`.
    apply ha 
    linarith

  have h3 : a = x * b := by 
    have eq1 : x = a / b := hx 
    have eq5 : (a / b) * b = a := by 
      field_simp [hb] 
    calc 
      a = (a / b) * b := by linarith [eq5]
      _ = x * b := by 
        rw [eq1]

  have h4 : a + b = (x + 1) * b := by 
    have ha1 : a = x * b := h3 
    calc 
      a + b = x * b + b := by 
        rw [ha1] 
      _ = (x + 1) * b := by 
        ring 

  have h5 : a - b = (x - 1) * b := by 
    have ha1 : a = x * b := h3 
    linarith

  rw [h4, h5] 
  have hx2 : x - 1 ≠ 0 := h2 
  field_simp [(show b ≠ 0 by exact hb), hx2]
  <;> ring