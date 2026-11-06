import Mathlib

theorem algebra_151563 (a : Fin 4 → ℝ) (ha : ∀ i j, i < j → a i > a j) :
    ∃ x y, x ≠ y ∧ x ^ 2 - (∑ i, a i) * x + a 0 * a 2 + a 1 * a 3 = 0 ∧
    y ^ 2 - (∑ i, a i) * y + a 0 * a 2 + a 1 * a 3 = 0 := by

  have ha1 : a 0 > a 1 := by apply ha 0 1; simp
  have ha2 : a 1 > a 2 := by apply ha 1 2; simp
  have ha3 : a 2 > a 3 := by apply ha 2 3; simp

  have h1 : a 0 - a 1 > 0 := sub_pos.mpr ha1
  have h2 : a 1 - a 2 > 0 := sub_pos.mpr ha2
  have h3 : a 2 - a 3 > 0 := sub_pos.mpr ha3

  have h10 : (a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3) > 0 := by
    nlinarith [sq_nonneg (a 0 - a 1 - a 2 + a 3), sq_nonneg (a 0 - a 1 + a 2 - a 3), sq_nonneg (a 0 + a 1 - a 2 - a 3),
        sq_nonneg (a 0 - a 3), sq_nonneg (a 1 - a 2),
        sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3, mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3
    ]
  use ( (a 0 + a 1 + a 2 + a 3) + Real.sqrt ((a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3)) ) / 2,
    ( (a 0 + a 1 + a 2 + a 3) - Real.sqrt ((a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3)) ) / 2
  constructor
  · -- Show that x ≠ y
    by_contra h
    have h_eq : Real.sqrt ((a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3)) = 0 := by
      nlinarith
    have h_pos : 0 < Real.sqrt ((a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3)) := by
      apply Real.sqrt_pos.mpr
      linarith [h10]
    linarith [h_eq, h_pos]
  constructor
  · -- Show that x is a solution
    have h11 : ∑ i : Fin 4, a i = a 0 + a 1 + a 2 + a 3 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    rw [h11]
    nlinarith [Real.sqrt_nonneg ((a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3)), Real.sq_sqrt (show (0 : ℝ) ≤ (a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3) by linarith [h10] ) ]
  · -- Show that y is a solution
    have h11 : ∑ i : Fin 4, a i = a 0 + a 1 + a 2 + a 3 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    rw [h11]
    nlinarith [Real.sqrt_nonneg ((a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3)), Real.sq_sqrt (show (0 : ℝ) ≤ (a 0 + a 1 + a 2 + a 3) ^ 2 - 4 * (a 0 * a 2 + a 1 * a 3) by linarith [h10] ) ]