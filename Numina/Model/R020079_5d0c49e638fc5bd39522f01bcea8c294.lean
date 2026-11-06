import Mathlib

open Real Matrix

theorem calculus_11176 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃! x : ℝ, Matrix.det (fun i j : Fin 3 => if i = 0 ∧ j = 0 then x else if i = 0 ∧ j = 1 then c else if i = 0 ∧ j = 2 then -b else if i = 1 ∧ j = 0 then -c else if i = 1 ∧ j = 1 then x else if i = 1 ∧ j = 2 then a else if i = 2 ∧ j = 0 then b else if i = 2 ∧ j = 1 then -a else x) = 0 := by
  use 0 
  constructor 
  · -- Show 0 is a solution
    simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul]
    <;> ring
  · -- Show that 0 is the unique solution 
    intro y hy
    simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul] at hy
    have h1 : y * (y ^ 2 + a ^ 2 + b ^ 2 + c ^ 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h1) with h2 h3
    · -- Case h2 : y = 0 
      linarith
    · -- Case h3 : y ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 = 0 
      have h4 : y ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 > 0 := by
        have ha2 : a ^ 2 > 0 := by
          exact sq_pos_of_ne_zero (show (a : ℝ) ≠ 0 by simpa using ha)
        have hb2 : b ^ 2 > 0 := by 
          exact sq_pos_of_ne_zero (show (b : ℝ) ≠ 0 by simpa using hb)
        have hc2 : c ^ 2 > 0 := by 
          exact sq_pos_of_ne_zero (show (c : ℝ) ≠ 0 by simpa using hc)
        have hy2 : y ^ 2 ≥ 0 := by
          exact sq_nonneg y
        linarith
      linarith