import Mathlib

theorem algebra_317 (A B C D : ℝ × ℝ) (hA : A = (0, 1)) (hB : B = (2, 5)) (hC : C = (5, 2)) (hD : D = (7, 0)) : ∃ a b : ℤ, (Real.sqrt ((dist A.1 B.1) ^ 2 + (dist A.2 B.2) ^ 2) + Real.sqrt ((dist B.1 C.1) ^ 2 + (dist B.2 C.2) ^ 2) + Real.sqrt ((dist C.1 D.1) ^ 2 + (dist C.2 D.2) ^ 2) + Real.sqrt ((dist D.1 A.1) ^ 2 + (dist D.2 A.2) ^ 2)) = a * Real.sqrt 2 + b * Real.sqrt 5 ∧ a + b = 12 := by

  use 10, 2
  have h1 : Real.sqrt ((dist A.1 B.1) ^ 2 + (dist A.2 B.2) ^ 2) = Real.sqrt 20 := by
    rw [hA, hB]
    simp [dist]
    all_goals norm_num

  have h2 : Real.sqrt ((dist B.1 C.1) ^ 2 + (dist B.2 C.2) ^ 2) = Real.sqrt 18 := by
    rw [hB, hC]
    simp [dist]
    all_goals norm_num

  have h3 : Real.sqrt ((dist C.1 D.1) ^ 2 + (dist C.2 D.2) ^ 2) = Real.sqrt 8 := by
    rw [hC, hD]
    simp [dist]
    all_goals norm_num

  have h4 : Real.sqrt ((dist D.1 A.1) ^ 2 + (dist D.2 A.2) ^ 2) = Real.sqrt 50 := by
    rw [hD, hA]
    simp [dist]
    all_goals norm_num

  rw [h1, h2, h3, h4]
  have h5 : Real.sqrt (20 : ℝ) = 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h6 : Real.sqrt (18 : ℝ) = 3 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h7 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h8 : Real.sqrt (50 : ℝ) = 5 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  rw [h5, h6, h7, h8]
  constructor
  · -- Show that the equality holds
    ring_nf
  · -- Show that the sum is 12
    norm_num