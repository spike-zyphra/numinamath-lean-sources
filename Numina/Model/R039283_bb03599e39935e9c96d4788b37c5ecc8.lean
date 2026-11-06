import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_191285 (f : ℝ → ℝ) (hf : f = λ x => (x^4 - x^2) / (x^6 + 2 * x^3 - 1)) :
    IsGreatest {y | ∃ x, x > 1 ∧ f x = y} (1 / 6) := by
  constructor
  · -- Show that 1/6 is achievable, using x = (1 + sqrt(5))/2.
    use (1 + Real.sqrt 5) / 2
    constructor
    · -- Show x > 1
      have h1 : Real.sqrt 5 > 1 := by
        nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5: ℝ) by norm_num)]
      linarith
    · -- Show f((1 + Real.sqrt 5) / 2) = 1 / 6
      have eq2 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := by 
        nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5: ℝ) by norm_num)]
      have eq3 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 = ((1 + Real.sqrt 5) / 2 + 1) * ((1 + Real.sqrt 5) / 2) := by
        calc
          ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3
            = ((1 + Real.sqrt 5) / 2 : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 := by ring
          _ = ((1 + Real.sqrt 5) / 2 : ℝ) * ((1 + Real.sqrt 5) / 2 + 1) := by rw [eq2]
          _ = ((1 + Real.sqrt 5) / 2 + 1) * ((1 + Real.sqrt 5) / 2) := by ring 
      have eq4 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 4 = ((1 + Real.sqrt 5) / 2 + 1) ^ 2 := by 
        calc 
          ((1 + Real.sqrt 5) / 2 : ℝ) ^ 4 
            = (((1 + Real.sqrt 5) / 2 : ℝ) ^ 2) ^ 2 := by ring
          _ = ((1 + Real.sqrt 5) / 2 + 1) ^ 2 := by rw [eq2]
      have eq5 : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 6 = ((1 + Real.sqrt 5) / 2 + 1) ^ 3 := by
        calc 
          ((1 + Real.sqrt 5) / 2 : ℝ) ^ 6 
            = (((1 + Real.sqrt 5) / 2 : ℝ) ^ 2) ^ 3 := by ring
          _ = ((1 + Real.sqrt 5) / 2 + 1) ^ 3 := by rw [eq2]
      have eq3' : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 4 - ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 + ((1 + Real.sqrt 5) / 2 : ℝ) := by
        rw [eq4]
        nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg ((1 + Real.sqrt 5) / 2 : ℝ), sq_nonneg ((1 + Real.sqrt 5) / 2 - 1 : ℝ)]
      have eq4' : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 6 + 2 * ((1 + Real.sqrt 5) / 2 : ℝ) ^ 3 - 1 = 6 * (((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 + ((1 + Real.sqrt 5) / 2 : ℝ)) := by
        rw [eq5, eq3]
        nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg ((1 + Real.sqrt 5) / 2 : ℝ), sq_nonneg ((1 + Real.sqrt 5) / 2 - 1 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (5: ℝ) by norm_num)]
      have eq5' : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 + ((1 + Real.sqrt 5) / 2 : ℝ) > 0 := by 
        nlinarith [Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5: ℝ) by norm_num)]
      rw [hf]
      simp only [eq3', eq4']
      field_simp [eq5']
      <;> ring_nf <;> norm_num [sq_nonneg ((1 + Real.sqrt 5) / 2 : ℝ), sq_nonneg ((1 + Real.sqrt 5) / 2 ^ 2 : ℝ)]
      <;> ring
  · -- Show that 1/6 is the greatest
    intro y
    rintro ⟨x, hx, h_eq⟩
    rw [hf] at h_eq
    have h_eq' : ((x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1)) = y := h_eq
    have hx1 : x ^ 6 + 2 * x ^ 3 - 1 > 0 := by
      have h1 : x ^ 2 > 1 := by nlinarith
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 3 - 1), sq_nonneg (x + 1), sq_nonneg (x ^ 2), sq_nonneg (x ^ 3), sq_pos_of_pos (show x > 0 by nlinarith), mul_pos (show (0:ℝ) < x by nlinarith) (show (0:ℝ) < x by nlinarith)]
    have eq2 : (x ^ 4 - x ^ 2) = y * (x ^ 6 + 2 * x ^ 3 - 1) := by
      have h1 : x ^ 6 + 2 * x ^ 3 - 1 ≠ 0 := by linarith
      field_simp [h1] at h_eq' ⊢
      <;> nlinarith
    have h_eq2 : (x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1) ≤ 1 / 6 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (x ^ 2 - ((1 + Real.sqrt 5) / 2 ) ^ 2), sq_nonneg (x ^ 2 - ((1 + Real.sqrt 5) / 2 )), sq_nonneg (x * (x ^ 2 - x - 1)), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 - x), sq_nonneg (x * (x - ((1 + Real.sqrt 5) / 2 )) ), sq_nonneg (x * (x - 1)), sq_nonneg (( (1 + Real.sqrt 5) / 2 )^2 - x^2), sq_nonneg (x^2 * (x - 1)), mul_nonneg (show (0 : ℝ) ≤ x ^ 2 by positivity) (show (0 : ℝ) ≤ (x ^ 2 - x - 1) ^ 2 by positivity), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.mul_self_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
      ]
    have h_eq3 : (x ^ 4 - x ^ 2) / (x ^ 6 + 2 * x ^ 3 - 1) = y := by
      linarith [h_eq']
    linarith [h_eq2, h_eq3]