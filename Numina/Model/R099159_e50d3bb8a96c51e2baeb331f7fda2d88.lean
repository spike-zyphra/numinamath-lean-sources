import Mathlib

theorem algebra_116277 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / (a + b + c) = 1) (h2 : 1 / (a + c) = 1.5)
    (h3 : 1 / (b + c) = 2) :
    1 / (a + b) = 1.2 := by

  -- First, ensure denominators are non-zero

  have h1' : a + b + c ≠ 0 := by
    by_contra h
    rw [h] at h1
    norm_num at h1

  have h2' : a + c ≠ 0 := by
    by_contra h
    rw [h] at h2
    norm_num at h2

  have h3' : b + c ≠ 0 := by
    by_contra h
    rw [h] at h3
    norm_num at h3

  -- Now reciprocate the equations to linear form.

  have h4 : a + b + c = 1 := by
    have h1_ne_zero : a + b + c ≠ 0 := h1'
    field_simp at h1 ⊢
    linarith

  have h5 : a + c = (2 : ℝ) / 3 := by
    have h2_ne_zero : a + c ≠ 0 := h2'
    field_simp at h2 ⊢
    norm_num at h2 ⊢
    linarith

  have h6 : b + c = (1 : ℝ) / 2 := by
    have h3_ne_zero : b + c ≠ 0 := h3'
    field_simp at h3 ⊢
    norm_num at h3 ⊢
    linarith

  -- Solve the system of linear equations to find a + b.

  have h7 : a = (1 : ℝ) / 2 := by
    linarith [h4, h6]

  have h7' : b = (1 : ℝ) / 3 := by
    linarith [h4, h5]

  -- Add them up to get a + b = 5/6.

  have h8 : a + b = (5 : ℝ) / 6 := by
    linarith [h7, h7']

  -- Then reciprocate to get 1/(a + b) = 6/5.

  have h9 : 1 / (a + b) = (6 : ℝ) / 5 := by
    rw [h8]
    field_simp
    <;> norm_num

  -- Finally, converting 6/5 to decimal

  rw [h9]
  norm_num