import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_163534
  (a : Fin 3 → ℝ × ℝ)
  (ha : a 0 = (1, 5) ∧ a 1 = (4, -1) ∧ a 2 = (2, 1))
  (lambda : Fin 3 → ℝ)
  (hlambda : ∀ i, 0 ≤ lambda i)
  (hlambda' : lambda 0 + lambda 1 / 2 + lambda 2 / 3 = 1) :
  IsLeast {x | ∃ t : Fin 3 → ℝ,
    (∀ i, 0 ≤ t i) ∧ t 0 + t 1 / 2 + t 2 / 3 = 1 ∧
    x = Real.sqrt ((t 0 * (a 0).1 + t 1 * (a 1).1 + t 2 * (a 2).1)^2 +
      (t 0 * (a 0).2 + t 1 * (a 1).2 + t 2 * (a 2).2)^2)} (3 * Real.sqrt 2) := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  constructor
  · -- Show that 3 * Real.sqrt 2 is in the set
    use λ i =>
      match i with
      | 0 => 5 / 7
      | 1 => 4 / 7
      | 2 => 0
      | _ => 0
    constructor
    · intro i
      fin_cases i <;> norm_num
    constructor
    · norm_num
    · -- Now compute the value
      have ha01 : (a 0).1 = 1 := by
        simp [ha0]
      have ha02 : (a 0).2 = 5 := by
        simp [ha0]
      have ha11 : (a 1).1 = 4 := by
        simp [ha1]
      have ha12 : (a 1).2 = -1 := by
        simp [ha1]
      have ha21 : (a 2).1 = 2 := by
        simp [ha2]
      have ha22 : (a 2).2 = 1 := by
        simp [ha2]
      simp [ha01, ha02, ha11, ha12, ha21, ha22]
      have h1 : Real.sqrt ((5 / 7 * (1 : ℝ) + 4 / 7 * (4 : ℝ) + (0 : ℝ) * (2 : ℝ)) ^ 2 + (5 / 7 * (5 : ℝ) + 4 / 7 * (-1 : ℝ) + (0 : ℝ) * (1 : ℝ)) ^ 2) = 3 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      linarith
  · -- Show $3 * \sqrt{2}$ is the least element
    rintro x ⟨t, ht_nonneg, ht_sum, hx⟩
    have ha01 : (a 0).1 = 1 := by
      simp [ha0]
    have ha02 : (a 0).2 = 5 := by
      simp [ha0]
    have ha11 : (a 1).1 = 4 := by
      simp [ha1]
    have ha12 : (a 1).2 = -1 := by
      simp [ha1]
    have ha21 : (a 2).1 = 2 := by
      simp [ha2]
    have ha22 : (a 2).2 = 1 := by
      simp [ha2]
    have h1 : x = Real.sqrt ((t 0 * (a 0).1 + t 1 * (a 1).1 + t 2 * (a 2).1)^2 + (t 0 * (a 0).2 + t 1 * (a 1).2 + t 2 * (a 2).2)^2) := by
      linarith [hx]
    have hx1 : x = Real.sqrt ((t 0 * 1 + t 1 * 4 + t 2 * 2) ^ 2 + (t 0 * 5 + t 1 * (-1) + t 2 * 1) ^ 2) := by
      rw [h1]
      simp [ha01, ha02, ha11, ha12, ha21, ha22]
    have h2 : (t 0 * 1 + t 1 * 4 + t 2 * 2) ^ 2 + (t 0 * 5 + t 1 * (-1) + t 2 * 1) ^ 2 ≥ 18 := by
      have h2 : t 0 ≥ 0 := ht_nonneg 0
      have h3 : t 1 ≥ 0 := ht_nonneg 1
      have h4 : t 2 ≥ 0 := ht_nonneg 2
      nlinarith [sq_nonneg (t 0 - 5 / 7), sq_nonneg (t 1 - 4 / 7), sq_nonneg (t 2 - 0), 
        ht_sum, mul_nonneg (ht_nonneg 0) (ht_nonneg 1), mul_nonneg (ht_nonneg 0) (ht_nonneg 2), mul_nonneg (ht_nonneg 1) (ht_nonneg 2)]
    have h3 : x ≥ Real.sqrt 18 := by
      rw [hx1]
      have h4 : Real.sqrt ((t 0 * 1 + t 1 * 4 + t 2 * 2) ^ 2 + (t 0 * 5 + t 1 * (-1) + t 2 * 1) ^ 2) ≥ Real.sqrt (18 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith [h2]
      linarith
    have h4 : Real.sqrt (18 : ℝ) = 3 * Real.sqrt 2 := by
      calc
        Real.sqrt (18 : ℝ) = Real.sqrt (3^2 * 2) := by norm_num
        _ = (3 : ℝ) * Real.sqrt 2 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    linarith