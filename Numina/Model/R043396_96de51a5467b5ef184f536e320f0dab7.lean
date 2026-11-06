import Mathlib

open Polynomial

theorem algebra_4316 {f : ℝ[X]} (hf : f.natDegree = 4) (h₁ : f.eval 1 = 1) (h₂ : f.eval 2 = 2) (h₃ : f.eval 3 = 3) (h₄ : f.eval 4 = 4) (h₅ : f.eval 5 = 29) : f.eval 6 = 126 := by
  have h6 : f.natDegree = 4 := hf
  have eq1_eq2 : f.eval 1 = ∑ i in Finset.range (f.natDegree + 1), f.coeff i * (1:ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h6]
    <;> norm_num
  have eq2_eq2 : f.eval 2 = ∑ i in Finset.range (f.natDegree + 1), f.coeff i * (2:ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h6]
    <;> norm_num
  have eq3_eq2 : f.eval 3 = ∑ i in Finset.range (f.natDegree + 1), f.coeff i * (3:ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h6]
    <;> norm_num
  have eq4_eq2 : f.eval 4 = ∑ i in Finset.range (f.natDegree + 1), f.coeff i * (4:ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h6]
    <;> norm_num
  have eq5_eq2 : f.eval 5 = ∑ i in Finset.range (f.natDegree + 1), f.coeff i * (5:ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h6]
    <;> norm_num
  have eq6_eq2 : f.eval 6 = ∑ i in Finset.range (f.natDegree + 1), f.coeff i * (6:ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h6]
    <;> norm_num
  rw [eq1_eq2] at h₁
  rw [eq2_eq2] at h₂
  rw [eq3_eq2] at h₃
  rw [eq4_eq2] at h₄
  rw [eq5_eq2] at h₅
  rw [eq6_eq2]
  simp [h6] at h₁ h₂ h₃ h₄ h₅ ⊢
  norm_num [Finset.sum_range_succ] at h₁ h₂ h₃ h₄ h₅ ⊢
  linarith