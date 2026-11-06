import Mathlib

theorem algebra_256596 {x y : ℝ} (h : x > 0 ∧ y > 0) (h1 : Real.sqrt x / Real.sqrt y = 5) :
    (x + y) / (2 * y) = 13 := by
  have h2 : Real.sqrt y > 0 := by
    exact Real.sqrt_pos.mpr h.2
  have h3 : Real.sqrt x = 5 * Real.sqrt y := by
    field_simp [h2] at h1
    all_goals
      nlinarith
  have h4 : x = 25 * y := by
    calc
      x = (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [h.1]
      _ = (5 * Real.sqrt y) ^ 2 := by
        rw [h3]
      _ = 25 * (Real.sqrt y ^ 2) := by
        ring_nf
      _ = 25 * y := by
        have h5 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (show 0 ≤ y by linarith [h.2])
        rw [h5]
        all_goals linarith
  rw [show x = 25 * y by linarith [h4]]
  -- Now (25 * y + y) / (2 * y)
  have h6 : y > 0 := h.2
  field_simp [h6]
  <;> nlinarith [h6]
  <;> ring_nf
  <;> nlinarith [h6]
  all_goals
    try { tauto }
    <;> try { nlinarith [h6] }