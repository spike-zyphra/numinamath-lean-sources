import Mathlib

/-
4. Determine the integer numbers $x$ and $y$ for which:

$$
\|x-3|+| y-2 x\|=3
$$

Supliment, G.M., November 2013
-/

theorem algebra_119778 (x y : ℤ):
abs ( |x-3|+|y-2*x| ) = 3 
↔
(x=3 ∧ y=9) ∨ (x=3 ∧ y=3) ∨ (x=4 ∧ y=10) ∨ (x=4 ∧ y=6) ∨ (x=2 ∧ y=6) ∨ (x=2 ∧ y=2) ∨ (x=5 ∧ y=11) ∨ (x=5 ∧ y=9) ∨ (x=1 ∧ y=3) ∨ (x=1 ∧ y=1) ∨ (x=0 ∧ y=0) ∨ (x=6 ∧ y=12) := by

  --Note that |x-3|+|y-2*x| is always non-negative, so the last absolute value is redundant.
  have : abs ( |x-3|+|y-2*x| ) = |x-3|+|y-2*x| := by
    have : 0 ≤ |x - 3| + |y - 2 * x| := by 
      have t1: 0 ≤ |x - 3| := by exact abs_nonneg (x - 3)
      have t2: 0 ≤ |y - 2 * x| := by exact abs_nonneg (y - 2 * x)
      exact Int.add_nonneg t1 t2
    exact abs_of_nonneg this
  rw [this]


  constructor

  --Frome left to right, we have that |x-3| ∈ [0,3] and we check each value separately.
  intro h
  have lb : 0 ≤ |x-3| := by exact abs_nonneg (x - 3)
  have ub : |x-3| ≤ 3 := by
    have : 0 ≤ |y - 2 * x| := by exact abs_nonneg (y - 2 * x)
    linarith
  have t1 : x - 3 ≤ 3 := by exact sub_le_of_abs_sub_le_right ub 
  have t2 : -3 ≤ x-3 := by exact neg_le_of_abs_le ub
  have : -3 ≤ x - 3 ∧ x - 3 ≤ 3 := ⟨t2,t1⟩
  have xl: 0 ≤ x := by omega
  have xu: x ≤ 6 := by omega

  interval_cases x <;> simp_all 

  have : |y-2| = 1 := by linarith only [h]
  rw [abs_eq] at this
  omega
  norm_num

  have : |y-4| = 2 := by linarith only [h]
  rw [abs_eq] at this
  omega
  norm_num

  have : |y-6| = 3 := by linarith only [h]
  rw [abs_eq] at this
  omega
  norm_num

  have : |y-8| = 2 := by linarith only [h]
  rw [abs_eq] at this
  omega
  norm_num

  have : |y-10| = 1 := by linarith only [h]
  rw [abs_eq] at this
  omega
  norm_num

  linarith only [h]
  
  --From right to left, simple verification.
  intro h
  rcases h with ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ <;>
  simp [ae,be]

