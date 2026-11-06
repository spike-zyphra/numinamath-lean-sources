import Mathlib
open Real
set_option maxHeartbeats 800000
theorem algebra_276278 {A B : ℝ} (hA : A ≥ 0) (hB : B ≥ 0)
    (hAB : A^2 ≥ B) :
    √(A + √B) = √((A + √(A^2 - B)) / 2) +
    √((A - √(A^2 - B)) / 2) ∧
    √(A - √B) = √((A + √(A^2 - B)) / 2) -
    √((A - √(A^2 - B)) / 2) := by
  have hB' : √B ≥ 0 := Real.sqrt_nonneg B
  have h1 : A + √B ≥ 0 := by
    linarith [hA, hB']
  have h2 : A - √B ≥ 0 := by
    have h3 : √B ≤ A := by
      nlinarith [Real.sqrt_nonneg B, Real.sq_sqrt (show 0 ≤ (B : ℝ) by linarith), hA, hAB]
    linarith [h3, hA]
  have h3 : 0 ≤ √((A + √(A ^ 2 - B)) / 2) := Real.sqrt_nonneg ((A + √(A ^ 2 - B)) / 2)
  have h4 : 0 ≤ √((A - √(A ^ 2 - B)) / 2) := Real.sqrt_nonneg ((A - √(A ^ 2 - B)) / 2)
  have h5 : (A + √(A ^ 2 - B)) / 2 ≥ 0 := by
    have h6 : √(A ^ 2 - B) ≥ 0 := Real.sqrt_nonneg (A ^ 2 - B)
    nlinarith [show A ≥ 0 from hA, h6]
  have h6' : (A - √(A ^ 2 - B)) / 2 ≥ 0 := by
    have h7 : √(A ^ 2 - B) ≤ A := by
      have h8 : (√(A ^ 2 - B)) ^ 2 ≤ A ^ 2 := by
        nlinarith [Real.sqrt_nonneg (A ^ 2 - B), Real.sq_sqrt (show (A ^ 2 - B : ℝ) ≥ 0 by nlinarith), hA]
      nlinarith [Real.sqrt_nonneg (A ^ 2 - B), hA]
    nlinarith [show A ≥ 0 from hA, h7, Real.sqrt_nonneg (A ^ 2 - B)]
  have h12 : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) ) * (Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) = Real.sqrt B / 2 := by
    have h7' : Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) * Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) = Real.sqrt (( (A + Real.sqrt (A ^ 2 - B)) / 2 ) * ( (A - Real.sqrt (A ^ 2 - B)) / 2 )) := by 
      rw [← Real.sqrt_mul (by nlinarith)]
    rw [h7'] 
    have h8' : ( (A + Real.sqrt (A ^ 2 - B)) / 2 ) * ( (A - Real.sqrt (A ^ 2 - B)) / 2 ) = (B / 4) := by
      nlinarith [Real.sqrt_nonneg (A ^ 2 - B), Real.sq_sqrt (show 0 ≤ (A ^ 2 - B : ℝ) by nlinarith)]
    rw [h8']
    have h9' : Real.sqrt ((B / 4) ) = Real.sqrt B / 2 := by
      have h10' : Real.sqrt (B / (4 : ℝ)) = Real.sqrt B / Real.sqrt (4 : ℝ) := by
        field_simp [Real.sqrt_div]
      have h11' : Real.sqrt ((4 : ℝ)) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h11'] at h10'
      have h12' : Real.sqrt B / (2 : ℝ) = Real.sqrt B / 2 := by
        ring
      rw [h12'] at h10'
      linarith
    exact h9'
  have h7 : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) + Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ^ 2 = A + Real.sqrt B := by
    have h8 : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2 ) ) ^ 2 = (A + Real.sqrt (A ^ 2 - B)) / 2 := Real.sq_sqrt (by linarith)
    have h9 : (Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2 ) ) ^ 2 = (A - Real.sqrt (A ^ 2 - B)) / 2 := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg B, Real.sqrt_nonneg (A ^ 2 - B), h12, Real.sq_sqrt (show 0 ≤ (B : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (A ^ 2 - B : ℝ) by nlinarith)]
  have h7'' : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) - Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ^ 2 = A - Real.sqrt B := by
    have h8'' : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2 ) ) ^ 2 = (A + Real.sqrt (A ^ 2 - B)) / 2 := Real.sq_sqrt (by linarith)
    have h9'' : (Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2 ) ) ^ 2 = (A - Real.sqrt (A ^ 2 - B)) / 2 := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg B, Real.sqrt_nonneg (A ^ 2 - B), h12, Real.sq_sqrt (show 0 ≤ (B : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (A ^ 2 - B : ℝ) by nlinarith)]
  have h9'' : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) - Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ≥ 0 := by
    have h5' : Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) ≥ Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) := by
      apply Real.sqrt_le_sqrt
      have h7 : (A + Real.sqrt (A^2 - B)) / 2 ≥ (A - Real.sqrt (A^2 - B)) / 2 := by
        have h8 : Real.sqrt (A^2 - B) ≥ 0 := Real.sqrt_nonneg (A ^ 2 - B)
        nlinarith [h8, Real.sq_sqrt (show (A ^ 2 - B : ℝ) ≥ 0 by nlinarith)]
      linarith
    linarith [Real.sqrt_nonneg ((A - Real.sqrt (A ^ 2 - B)) / 2), h5']
  constructor
  · -- Prove the first equality
    have h8' : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) + Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ≥ 0 := by
      positivity
    have h9' : Real.sqrt ((Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) + Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ^ 2) = Real.sqrt (A + Real.sqrt B) := by
      rw [h7]
    have h10' : Real.sqrt ((Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) + Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ^ 2) = (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) + Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) := by
      rw [Real.sqrt_sq (by positivity)]
    have eq1 : Real.sqrt ((A + Real.sqrt B) ) = (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) + Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) := by
      nlinarith [h9', h10']
    linarith [eq1, Real.sqrt_nonneg (A + Real.sqrt B), Real.sqrt_nonneg (A - Real.sqrt B), Real.sqrt_nonneg (A^2 - B)]
  · -- Prove the second equality
    have h8' : (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) - Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ≥ 0 := h9''
    have h9' : Real.sqrt ((Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) - Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ^ 2) = Real.sqrt (A - Real.sqrt B) := by
      rw [h7'']
    have h10' : Real.sqrt ((Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) - Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) ^ 2) = (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) - Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) := by
      rw [Real.sqrt_sq (by linarith)]
    have eq1 : Real.sqrt (A - Real.sqrt B) = (Real.sqrt ((A + Real.sqrt (A ^ 2 - B)) / 2) - Real.sqrt ((A - Real.sqrt (A ^ 2 - B)) / 2) ) := by
      nlinarith [h9', h10']
    linarith [eq1, Real.sqrt_nonneg (A + Real.sqrt B), Real.sqrt_nonneg (A - Real.sqrt B), Real.sqrt_nonneg (A^2 - B)]