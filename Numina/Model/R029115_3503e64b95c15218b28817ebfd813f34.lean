import Mathlib

theorem algebra_325307 {x a : ℝ} (h : 0 ≤ x) (ha : 0 < a) (h1 : Real.sqrt x = 1 / Real.sqrt a - Real.sqrt a) :
    Real.sqrt (4 * x + x ^ 2) = 1 / a - a := by
  have h2 : 0 < Real.sqrt a := by
    apply Real.sqrt_pos.2
    linarith
  have h3 : x = (1 / Real.sqrt a - Real.sqrt a) ^ 2 := by
    calc
      x = (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (1 / Real.sqrt a - Real.sqrt a) ^ 2 := by
        rw [h1]
  have h4 : x = a + 1 / a - 2 := by
    rw [h3]
    have h5 : (1 / Real.sqrt a - Real.sqrt a) ^ 2 = (1 / Real.sqrt a) ^ 2 - 2 * (1 / Real.sqrt a * Real.sqrt a) + (Real.sqrt a) ^ 2 := by ring
    rw [h5]
    have h6 : (1 / Real.sqrt a) ^ 2 = 1 / a := by
      have h6 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
      field_simp [h6]
    have h7 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
    have h8 : (1 / Real.sqrt a * Real.sqrt a) = 1 := by
      field_simp [show 0 < Real.sqrt a by linarith [h2]]
    rw [h6, h8, h7]
    ring
  -- Compute $4x + x^2$.
  have h5 : 0 < a := ha
  have h6 : 4 * x + x ^ 2 = (a - 1 / a) ^ 2 := by
    rw [h4]
    field_simp
    <;> ring
  have h7 : Real.sqrt (4 * x + x ^ 2) = Real.sqrt ((a - 1 / a) ^ 2) := by
    rw [h6]
  have h8 : Real.sqrt ((a - 1 / a) ^ 2) = abs (a - 1 / a) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h7, h8]
  -- Now we need to determine the sign
  have h9 : a ≤ 1 := by
    have h10 : Real.sqrt x ≥ 0 := by
      apply Real.sqrt_nonneg
    have h11 : (1 / Real.sqrt a - Real.sqrt a) ≥ 0 := by
      linarith [h1, h10]
    have h12 : 0 < Real.sqrt a := by
      apply Real.sqrt_pos.2
      linarith
    have h13 : (1 / Real.sqrt a) ≥ Real.sqrt a := by
      have h14 : (1 / Real.sqrt a - Real.sqrt a) ≥ 0 := h11
      linarith
    have h14 : (1 / Real.sqrt a) * Real.sqrt a = 1 := by
      field_simp [h12]
    have h15 : (Real.sqrt a) * (Real.sqrt a) = a := by
      have h16 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
      linarith
    have h16 : (1 / Real.sqrt a) * Real.sqrt a ≥ Real.sqrt a * Real.sqrt a := by
      have h17 : (1 / Real.sqrt a) ≥ Real.sqrt a := h13
      have h18 : Real.sqrt a ≥ 0 := by
        apply Real.sqrt_nonneg
      nlinarith
    have h17 : (1 / Real.sqrt a) * Real.sqrt a = 1 := h14
    have h18 : Real.sqrt a * Real.sqrt a = a := by
      have h19 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
      linarith
    nlinarith [h17, h18, h16]
  have h10 : a - 1 / a ≤ 0 := by
    have h11 : a ≤ 1 := h9
    have h12 : 0 < a := ha
    have h14 : 1 / a ≥ a := by
      have h15 : a ≤ 1 := h9
      have h16 : 0 < a := ha
      have h17 : 1 / a ≥ a := by
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith [h15]
      linarith
    have h15 : 1 / a ≥ a := h14
    have h16 : a - 1 / a ≤ 0 := by
      linarith
    linarith
  have h11 : abs (a - 1 / a) = 1 / a - a := by
    have h12 : a - 1 / a ≤ 0 := h10
    rw [abs_of_nonpos h12]
    all_goals linarith
  rw [h11]
  all_goals linarith