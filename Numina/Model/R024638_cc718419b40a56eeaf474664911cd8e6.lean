import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_120048
  (a : Fin 3 → ℝ × ℝ)
  (ha : a 0 = (1, 5) ∧ a 1 = (4, -1) ∧ a 2 = (2, 1))
  (lambda : Fin 3 → ℝ)
  (hlambda : ∀ i, 0 ≤ lambda i)
  (hlambda' : lambda 0 + lambda 1 / 2 + lambda 2 / 3 = 1) :
  IsLeast {x | ∃ t : Fin 3 → ℝ,
    (∀ i, 0 ≤ t i) ∧ t 0 + t 1 / 2 + t 2 / 3 = 1 ∧
    x = sqrt ((t 0 * (a 0).1 + t 1 * (a 1).1 + t 2 * (a 2).1)^2 +
      (t 0 * (a 0).2 + t 1 * (a 1).2 + t 2 * (a 2).2)^2)} (3 * Real.sqrt 2) := by

  have ha1 : a 0 = (1, 5) := by tauto
  have ha2 : a 1 = (4, -1) := by tauto
  have ha3 : a 2 = (2, 1) := by tauto

  constructor
  · -- Show that 3 * Real.sqrt 2 is in the set.
    use λ i =>
      match i with
      | 0 => (5 / 7)
      | 1 => (4 / 7)
      | 2 => (0)
      | _ => (0)
    constructor
    · -- Show that all coefficients are non-negative
      intro i
      fin_cases i <;> norm_num
    constructor
    · -- Show that the coefficients satisfy the division constraint.
      norm_num
    · -- Show that the value equals the squared root.
      rw [ha1] at *
      rw [ha2] at *
      rw [ha3] at *
      have h1 : (5 / 7 : ℝ) * (1 : ℝ) + (4 / 7 : ℝ) * (4 : ℝ) + (0 : ℝ) * (2 : ℝ) = (3 : ℝ) := by norm_num
      have h2 : (5 / 7 : ℝ) * (5 : ℝ) + (4 / 7 : ℝ) * (-1 : ℝ) + (0 : ℝ) * (1 : ℝ) = (3 : ℝ) := by norm_num
      have h3 : ((3 : ℝ)) ^ 2 + ((3 : ℝ)) ^ 2 = (18 : ℝ) := by norm_num
      have h4 : ((5 / 7 : ℝ) * (1 : ℝ) + (4 / 7 : ℝ) * (4 : ℝ) + (0 : ℝ) * (2 : ℝ)) ^ 2 + 
        ((5 / 7 : ℝ) * (5 : ℝ) + (4 / 7 : ℝ) * (-1 : ℝ) + (0 : ℝ) * (1 : ℝ)) ^ 2 = (18 : ℝ) := by
        rw [h1, h2]
        all_goals linarith
      have h6 : sqrt (( (5 / 7 : ℝ) * (1 : ℝ) + (4 / 7 : ℝ) * (4 : ℝ) + (0 : ℝ) * (2 : ℝ) ) ^ 2 + 
          ( (5 / 7 : ℝ) * (5 : ℝ) + (4 / 7 : ℝ) * (-1 : ℝ) + (0 : ℝ) * (1 : ℝ) ) ^ 2 ) = Real.sqrt 18 := by
        rw [show ( (5 / 7 : ℝ) * (1 : ℝ) + (4 / 7 : ℝ) * (4 : ℝ) + (0 : ℝ) * (2 : ℝ) ) ^ 2 + 
            ( (5 / 7 : ℝ) * (5 : ℝ) + (4 / 7 : ℝ) * (-1 : ℝ) + (0 : ℝ) * (1 : ℝ) ) ^ 2 = (18 : ℝ) by
              linarith [h4] ]
      have h7 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h6, h7]
  · -- Show that 3 * Real.sqrt 2 is the least element in the set.
    rintro x ⟨t, ht_nonneg, ht_div, hx⟩
    rw [ha1] at *
    rw [ha2] at *
    rw [ha3] at *
    have ht0_nonneg : 0 ≤ t 0 := ht_nonneg 0
    have ht1_nonneg : 0 ≤ t 1 := ht_nonneg 1
    have ht2_nonneg : 0 ≤ t 2 := ht_nonneg 2
    have h1 : t 0 + t 1 / 2 + t 2 / 3 = 1 := ht_div
    have h2 : (t 0 * (1 : ℝ) + t 1 * (4 : ℝ) + t 2 * (2 : ℝ)) ^ 2 + 
      (t 0 * (5 : ℝ) + t 1 * (-1 : ℝ) + t 2 * (1 : ℝ)) ^ 2 ≥ (18 : ℝ) := by
      nlinarith [sq_nonneg (t 0 - 5 / 7), sq_nonneg (t 1 - 4 / 7), sq_nonneg (t 2 - 0), 
        h1, 
        mul_nonneg ht0_nonneg ht1_nonneg, mul_nonneg ht0_nonneg ht2_nonneg, 
        mul_nonneg ht1_nonneg ht2_nonneg
      ]
    have h3 : sqrt ((t 0 * (1 : ℝ) + t 1 * (4 : ℝ) + t 2 * (2 : ℝ)) ^ 2 + 
      (t 0 * (5 : ℝ) + t 1 * (-1 : ℝ) + t 2 * (1 : ℝ)) ^ 2 ) ≥ Real.sqrt 18 := by
      apply Real.sqrt_le_sqrt 
      linarith [h2]
    have h4 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    linarith [hx, h3, h4]