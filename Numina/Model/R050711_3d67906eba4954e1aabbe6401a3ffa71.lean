import Mathlib

theorem algebra_326193 {f : ℝ → ℝ} (h : ∀ x, f (x + 1006) = 1 / 2 + Real.sqrt (f x - (f x) ^ 2))
    (hf : f (-1005) = 3 / 4) : f 2013 = 1 / 2 + Real.sqrt 3 / 4 := by
  have h1 : f 1 = 1 / 2 + Real.sqrt 3 / 4 := by
    have eq1 : f 1 = 1 / 2 + Real.sqrt (f (-1005) - (f (-1005)) ^ 2) := by
      specialize h (-1005)
      norm_num at h ⊢
      linarith
    rw [hf] at eq1
    have sqrt_eq : Real.sqrt (3 / 4 - (3 / 4 : ℝ) ^ 2) = Real.sqrt 3 / 4 := by
      rw [show (3 / 4 : ℝ) - (3 / 4 : ℝ) ^ 2 = ((3 : ℝ) / 16) by norm_num]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [sqrt_eq] at eq1
    linarith
  have h2 : f 1007 = 3 / 4 := by
    have eq2 : f 1007 = 1 / 2 + Real.sqrt (f 1 - (f 1) ^ 2) := by
      specialize h 1
      norm_num at h ⊢
      linarith
    rw [h1] at eq2
    have sqrt_eq_2 : Real.sqrt ((1 / 2 + Real.sqrt 3 / 4) - (1 / 2 + Real.sqrt 3 / 4) ^ 2) = 1 / 4 := by
      have h3 : ((1 / 2 + Real.sqrt 3 / 4) - (1 / 2 + Real.sqrt 3 / 4) ^ 2 : ℝ) = (1 / 16 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      rw [h3]
      rw [show Real.sqrt (1 / 16 : ℝ) = 1 / 4 by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      ]
    rw [sqrt_eq_2] at eq2
    nlinarith
  have eq3 : f 2013 = 1 / 2 + Real.sqrt (f 1007 - (f 1007) ^ 2) := by
    specialize h 1007
    norm_num at h ⊢
    linarith
  rw [h2] at eq3
  have sqrt_eq_3 : Real.sqrt ((3 / 4 : ℝ) - (3 / 4 : ℝ) ^ 2) = Real.sqrt 3 / 4 := by
    rw [show (3 / 4 : ℝ) - (3 / 4 : ℝ) ^ 2 = ((3 : ℝ) / 16) by norm_num]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [sqrt_eq_3] at eq3
  linarith