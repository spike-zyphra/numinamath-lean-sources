import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_9487 {a b c d : ℕ → ℤ}
  (ha : ∀ n, 0 < a n)
  (hb : ∀ n, 0 < b n)
  (hc : ∀ n, 0 < c n)
  (hd : ∀ n, 0 < d n)
  (h : ∀ n, (1 + Real.sqrt 2 + Real.sqrt 7)^n = a n + b n * Real.sqrt 2 + c n * Real.sqrt 7 + d n * Real.sqrt 14) :
  Tendsto (λ n => (a n)^3 / (b n * c n * d n)) atTop (𝓝 14) := by
  have h1 := h 0
  have h1' : (1 + Real.sqrt 2 + Real.sqrt 7) ^ 0 = 1 := by
    simp
  rw [h1'] at h1
  have ha0 : 0 < a 0 := ha 0
  have hb0 : 0 < b 0 := hb 0
  have hc0 : 0 < c 0 := hc 0
  have hd0 : 0 < d 0 := hd 0
  have ha0' : a 0 ≥ 1 := by omega
  have hb0' : b 0 ≥ 1 := by omega
  have hc0' : c 0 ≥ 1 := by omega
  have hd0' : d 0 ≥ 1 := by omega
  have h3 : (a 0 : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (a 0 : ℤ) ≥ 1 by omega)
  have h6 : (b 0 : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (b 0 : ℤ) ≥ 1 by omega)
  have h7 : (c 0 : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (c 0 : ℤ) ≥ 1 by omega)
  have h8 : (d 0 : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (d 0 : ℤ) ≥ 1 by omega)
  have h9 : 0 < (Real.sqrt 2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h10 : 0 < (Real.sqrt 7 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h11 : 0 < (Real.sqrt 14 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h12 : (1 : ℝ) = (a 0 : ℝ) + (b 0 : ℝ) * (Real.sqrt 2) + (c 0 : ℝ) * (Real.sqrt 7) + (d 0 : ℝ) * (Real.sqrt 14) := by linarith 
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 7, Real.sqrt_nonneg 14, 
    Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num), 
    mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 7), 
    mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 14), 
    mul_nonneg (Real.sqrt_nonneg 7) (Real.sqrt_nonneg 14), 
    sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (Real.sqrt 7 - 1), sq_nonneg (Real.sqrt 14 - 1), 
    Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
    Real.sqrt_pos.mpr (show (0 : ℝ) < (7 : ℝ) by norm_num), 
    Real.sqrt_pos.mpr (show (0 : ℝ) < (14 : ℝ) by norm_num)
  ]