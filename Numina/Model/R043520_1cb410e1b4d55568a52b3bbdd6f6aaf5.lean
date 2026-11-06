import Mathlib

open EuclideanGeometry

theorem geometry_248074 {A B C P : ℂ} (hne : P ≠ A ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A)
  (hP : dist P B ^ 2 + dist P C ^ 2 < dist P A ^ 2) :
  dist B C ^ 2 < dist A C ^ 2 + dist B A ^ 2 := by 
  have h2 : dist P B = Complex.abs (P - B) := by
    simp [dist_eq_norm, Complex.norm_eq_abs]
  have h3 : dist P C = Complex.abs (P - C) := by
    simp [dist_eq_norm, Complex.norm_eq_abs]
  have h4 : dist P A = Complex.abs (P - A) := by
    simp [dist_eq_norm, Complex.norm_eq_abs]
  have h5 : dist B C = Complex.abs (B - C) := by 
    simp [dist_eq_norm, Complex.norm_eq_abs]
  have h6 : dist A C = Complex.abs (A - C) := by 
    simp [dist_eq_norm, Complex.norm_eq_abs]
  have h7 : dist B A = Complex.abs (B - A) := by 
    simp [dist_eq_norm, Complex.norm_eq_abs]
  have h8 : Complex.abs (P - B) ^ 2 + Complex.abs (P - C) ^ 2 < Complex.abs (P - A) ^ 2 := by
    rw [h2] at hP
    rw [h3] at hP
    rw [h4] at hP
    nlinarith
  rw [h5, h6, h7]
  have eq1 : Complex.abs (B - C) ^ 2 = (B.re - C.re) ^ 2 + (B.im - C.im) ^ 2 := by
    have h1 : Complex.abs (B - C) = Real.sqrt ((B.re - C.re) ^ 2 + (B.im - C.im) ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h1]
    rw [Real.sq_sqrt (by positivity)]
  have eq2 : Complex.abs (A - C) ^ 2 = (A.re - C.re) ^ 2 + (A.im - C.im) ^ 2 := by
    have h2 : Complex.abs (A - C) = Real.sqrt ((A.re - C.re) ^ 2 + (A.im - C.im) ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h2]
    rw [Real.sq_sqrt (by positivity)]
  have eq3 : Complex.abs (B - A) ^ 2 = (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 := by
    have h3 : Complex.abs (B - A) = Real.sqrt ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h3]
    rw [Real.sq_sqrt (by positivity)]
  have eq4 : Complex.abs (P - B) ^ 2 = (P.re - B.re) ^ 2 + (P.im - B.im) ^ 2 := by
    have h4 : Complex.abs (P - B) = Real.sqrt ((P.re - B.re) ^ 2 + (P.im - B.im) ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h4]
    rw [Real.sq_sqrt (by positivity)]
  have eq5 : Complex.abs (P - C) ^ 2 = (P.re - C.re) ^ 2 + (P.im - C.im) ^ 2 := by
    have h5 : Complex.abs (P - C) = Real.sqrt ((P.re - C.re) ^ 2 + (P.im - C.im) ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h5]
    rw [Real.sq_sqrt (by positivity)]
  have eq6 : Complex.abs (P - A) ^ 2 = (P.re - A.re) ^ 2 + (P.im - A.im) ^ 2 := by
    have h6 : Complex.abs (P - A) = Real.sqrt ((P.re - A.re) ^ 2 + (P.im - A.im) ^ 2) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h6]
    rw [Real.sq_sqrt (by positivity)]
  rw [eq1, eq2, eq3]
  rw [eq4] at h8
  rw [eq5] at h8
  rw [eq6] at h8
  nlinarith [sq_nonneg (B.re - A.re - (C.re - A.re)), sq_nonneg (B.im - A.im - (C.im - A.im)), sq_nonneg (B.re - C.re), sq_nonneg (B.im - C.im), sq_nonneg (P.re - A.re), sq_nonneg (P.im - A.im), sq_nonneg (P.re - B.re), sq_nonneg (P.im - B.im), sq_nonneg (P.re - C.re), sq_nonneg (P.im - C.im), sq_nonneg (A.re - B.re), sq_nonneg (A.im - B.im), sq_nonneg (C.re - P.re), sq_nonneg (C.im - P.im), sq_nonneg ((A.re - C.re) - (B.re - P.re)), sq_nonneg ((A.im - C.im) - (B.im - P.im))]