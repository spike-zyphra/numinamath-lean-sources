import Mathlib

theorem algebra_215591 (x y : ℤ) (hx : x > 0) (hy : y > 0): (x + y) + (x - y) + x * y + (x:ℝ) / y = 2009 ↔ x = 246 ∧ y = 6 := by
  constructor
  · -- Forward direction: given the equation, prove (x,y) = (246, 6)
    intro h
    have h1 : (y : ℝ) > 0 := by
      exact_mod_cast show (y : ℝ) > 0 by exact_mod_cast hy
    have eq1 : (x + y) + (x - y) + x * y + (x : ℝ) / y = (2 * (x : ℝ) + (x : ℝ) * (y : ℝ) + (x : ℝ) / (y : ℝ)) := by 
      ring_nf
    rw [eq1] at h
    have eq4 : (x : ℝ) * (y ^ 2 + 2 * y + 1) = 2009 * (y : ℝ) := by
      have eq6 : (y : ℝ) > 0 := by exact_mod_cast hy
      field_simp at h ⊢
      nlinarith [sq_nonneg (y : ℝ), sq_nonneg (x : ℝ)]
    have eq7 : x * (y ^ 2 + 2 * y + 1) = 2009 * y := by
      exact_mod_cast eq4
    have eq8 : x * (y + 1) ^ 2 = 2009 * y := by
      ring_nf at eq7 ⊢
      linarith
    have h2 : y ≤ 2009 := by 
      nlinarith [sq_nonneg (y : ℤ), sq_nonneg ((y + 1) : ℤ), sq_pos_of_pos hy, sq_pos_of_pos hx]
    interval_cases y <;> omega
  · -- Backward direction: if (x,y) = (246, 6), prove the equation
    rintro ⟨hx0, hy0⟩
    rw [hx0, hy0]
    norm_num