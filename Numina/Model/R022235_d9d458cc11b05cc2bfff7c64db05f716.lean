import Mathlib

theorem algebra_6332 {x : ℂ} (hx : x ^ 2 + x + 1 = 0) (hx2 : x ≠ 0):
    x ^ 4 + 1 / x ^ 4 = -1 := by

  have h1 : x + 1 / x = -1 := by
    have hne : x ≠ 0 := hx2
    have eq1 : x^2 + x + 1 = 0 := hx
    have eq2 : x + 1 + (1 / x) = 0 := by
      calc
        x + 1 + (1 / x) = (x^2 + x + 1) / x := by 
          field_simp [hne]
          <;> ring
        _ = (0) / x := by 
          rw [eq1]
        _ = 0 := by 
          simp [hne]

    calc
      x + 1 / x = (x + 1 + (1 / x)) - 1 := by ring
      _ = 0 - 1 := by 
        rw [eq2]
      _ = -1 := by ring

  have h2 : x ^ 2 + 1 / x ^ 2 = -1 := by 
    have hne : x ≠ 0 := hx2
    have h3 : x + 1 / x = -1 := h1 
    calc 
      x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by 
        field_simp [hne]
        <;> ring
      _ = (-1) ^ 2 - 2 := by 
        rw [h3]
      _ = 1 - 2 := by norm_num
      _ = -1 := by norm_num

  have h4 : x ^ 4 + 1 / x ^ 4 = -1 := by
    have hne : x ≠ 0 := hx2
    have h5 : x ^ 2 + 1 / x ^ 2 = -1 := h2
    calc
      x ^ 4 + 1 / x ^ 4 = (x ^ 2 + 1 / x ^ 2) ^ 2 - 2 := by
        field_simp [hne]
        <;> ring
      _ = (-1) ^ 2 - 2 := by 
        rw [h5]
      _ = 1 - 2 := by norm_num
      _ = -1 := by norm_num

  exact h4