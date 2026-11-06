import Mathlib

theorem algebra_2341 {a : ℝ} (ha : a < 0) : a * Real.sqrt (-1 / a) = -Real.sqrt (-a) := by
  have h1 : a < 0 := ha
  have h2 : -a > 0 := by nlinarith
  have h3 : -1 / a > 0 := by
    have h4 : a < 0 := h1
    have h5 : -a > 0 := h2
    have h6 : -1 / a = 1 / (-a) := by
      field_simp [(show a ≠ 0 by linarith)]
    rw [h6]
    positivity
  have h4 : Real.sqrt (-1 / a) ≥ 0 := by 
    apply Real.sqrt_nonneg
  have h5 : (Real.sqrt (-1 / a)) ^ 2 = -1 / a := by 
    rw [Real.sq_sqrt]
    linarith
  have h6 : (a * Real.sqrt (-1 / a)) ^ 2 = (-a) := by
    calc
      (a * Real.sqrt (-1 / a)) ^ 2 = a^2 * (Real.sqrt (-1 / a) ^ 2) := by 
        ring
      _ = a^2 * (-1 / a) := by 
        rw [h5]
      _ = -a := by 
        field_simp [(show a ≠ 0 by linarith)]
        <;> nlinarith
  have h7 : Real.sqrt (-a) ≥ 0 := by 
    apply Real.sqrt_nonneg
  have h8 : (Real.sqrt (-a)) ^ 2 = -a := by 
    rw [Real.sq_sqrt]
    linarith
  have h9 : a * Real.sqrt (-1 / a) ≤ 0 := by 
    have h4 : Real.sqrt (-1 / a) ≥ 0 := h4
    nlinarith
  have h10 : - Real.sqrt (-a) ≤ 0 := by 
    have h7 : Real.sqrt (-a) ≥ 0 := h7
    nlinarith
  have h11 : (a * Real.sqrt (-1 / a)) ^ 2 = (- Real.sqrt (-a)) ^ 2 := by 
    have eq1 : (a * Real.sqrt (-1 / a)) ^ 2 = (-a) := h6
    have eq2 : (- Real.sqrt (-a)) ^ 2 = (-a) := by 
      calc
        (- Real.sqrt (-a)) ^ 2 = (Real.sqrt (-a)) ^ 2 := by 
          ring
        _ = -a := by 
          rw [Real.sq_sqrt]
          all_goals linarith
    linarith [eq1, eq2]
  have h14 : a * Real.sqrt (-1 / a) = - Real.sqrt (-a) := by
    nlinarith [h11, h9, h10, Real.sqrt_nonneg (-1 / a), Real.sqrt_nonneg (-a), sq_nonneg (a * Real.sqrt (-1 / a) + Real.sqrt (-a))]
  exact h14