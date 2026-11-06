import Mathlib

theorem algebra_6643 {x : ℂ} (hx : x ≠ 0) (h : x + 1/x = -2) : x^2020 + 1/x^2020 = 2 := by
  have h1 : (x + 1)^2 = 0 := by
    have eq2 : x * (x + 1/x) + 2 * x = 0 := by
      have h2 : x + 1/x = -2 := h
      calc
        x * (x + 1/x) + 2 * x = x * (-2) + 2 * x := by rw [h2]
        _ = -2 * x + 2 * x := by ring
        _ = 0 := by ring
    have eq3 : x * (x + 1/x) = x^2 + 1 := by
      field_simp [hx]
      <;> ring
    rw [eq3] at eq2 
    have h2 : x^2 + 1 + 2 *x = 0 := by
      have h2' : x^2 +1 + 2 * x = 0 := by
        ring_nf at eq2 ⊢
        simpa using eq2
      exact h2'
    have h3 : x^2 + 2 *x +1 =0 := by
      calc
        x^2 + 2 *x +1 = (x^2 +1 + 2 *x) := by ring
        _ = 0 := h2
    have h4 : (x +1)^2 = 0 := by
      have h5 : (x +1)^2 = x^2 + 2 *x +1 := by ring
      rw [h5]
      exact h3
    exact h4
  have h5 : x + 1 = 0 := by
    apply pow_eq_zero 
    exact h1
  have h2 : x = -1 := by 
    calc
      x = (x +1) -1 := by ring_nf
      _ = (0) -1 := by rw [h5]
      _ = -1 := by ring
  rw [h2]
  norm_num