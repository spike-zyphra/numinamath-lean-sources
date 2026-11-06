import Mathlib

theorem algebra_327671 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (h1 : f 1 = 2)
    (h2 : ∀ x y, x ≠ 0 → y ≠ 0 → f (Real.sqrt (x ^ 2 + y ^ 2)) = f x * f y / (f x + f y)) :
    f 5 = 2 / 25 := by
  have hsqrt2 : f (Real.sqrt 2) = 1 := by
    specialize h2 1 1 (by norm_num) (by norm_num)
    have hsqrt2_eq : Real.sqrt (1 ^ 2 + 1 ^ 2) = Real.sqrt 2 := by norm_num
    rw [hsqrt2_eq] at h2
    rw [h1] at h2
    norm_num at h2 ⊢
    exact h2
  
  have hsqrt3 : f (Real.sqrt 3) = 2 / 3 := by
    specialize h2 (Real.sqrt 2) 1 (by positivity) (by norm_num)
    have hsqrt3_eq : Real.sqrt ((Real.sqrt 2 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = Real.sqrt 3 := by
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by positivity)
      rw [h1]
      norm_num
    rw [hsqrt3_eq] at h2
    rw [hsqrt2] at h2
    rw [h1] at h2
    norm_num at h2 ⊢
    exact h2
  
  have h2_eq : f 2 = 1 / 2 := by
    specialize h2 (Real.sqrt 2) (Real.sqrt 2) (by positivity) (by positivity)
    have h2_eq2 : Real.sqrt ((Real.sqrt 2 : ℝ) ^ 2 + (Real.sqrt 2 : ℝ) ^ 2) = (2 : ℝ) := by
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by positivity)
      rw [h1]
      norm_num
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2_eq2] at h2
    rw [hsqrt2] at h2
    norm_num at h2 ⊢
    exact h2
  
  have hsqrt5 : f (Real.sqrt 5) = 2 / 5 := by
    specialize h2 2 1 (by norm_num) (by norm_num)
    have hsqrt5_eq : Real.sqrt ((2 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = Real.sqrt 5 := by norm_num
    rw [hsqrt5_eq] at h2
    rw [h2_eq, h1] at h2
    norm_num at h2 ⊢
    exact h2
  
  have h3_eq : f 3 = 2 / 9 := by
    specialize h2 2 (Real.sqrt 5) (by norm_num) (by positivity)
    have h3_eq : Real.sqrt ((2 : ℝ) ^ 2 + (Real.sqrt 5 : ℝ) ^ 2) = (3 : ℝ) := by
      have h1 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)
      rw [h1]
      norm_num
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3_eq] at h2
    rw [h2_eq, hsqrt5] at h2
    norm_num at h2 ⊢
    exact h2

  have h2sqrt2 : f (2 * Real.sqrt 2) = 1 / 4 := by
    specialize h2 2 2 (by norm_num) (by norm_num)
    have h2sqrt2_eq : Real.sqrt ((2 : ℝ) ^ 2 + (2 : ℝ) ^ 2) = 2 * Real.sqrt 2 := by
      have h1 : Real.sqrt ((2 : ℝ) ^ 2 + (2 : ℝ) ^ 2) = Real.sqrt 8 := by norm_num
      rw [h1]
      have h2 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h2]
    rw [h2sqrt2_eq] at h2
    rw [h2_eq] at h2
    norm_num at h2 ⊢
    exact h2
  
  have h4_eq : f 4 = 1 / 8 := by
    specialize h2 (2 * Real.sqrt 2) (2 * Real.sqrt 2) (by positivity) (by positivity)
    have h4_eq : Real.sqrt ((2 * Real.sqrt 2 : ℝ) ^ 2 + (2 * Real.sqrt 2 : ℝ) ^ 2) = (4 : ℝ) := by
      have h1 : (2 * Real.sqrt 2 : ℝ) ^ 2 = 8 := by
        calc
          (2 * Real.sqrt 2 : ℝ) ^ 2 = 4 * (Real.sqrt 2 : ℝ) ^ 2 := by ring
          _ = 4 * 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
          _ = 8 := by norm_num
      rw [h1]
      norm_num
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h4_eq] at h2
    rw [h2sqrt2] at h2
    norm_num at h2 ⊢
    exact h2
  
  have h5_eq : f 5 = 2 / 25 := by
    specialize h2 3 4 (by norm_num) (by norm_num)
    have h5_eq : Real.sqrt ((3 : ℝ) ^ 2 + (4 : ℝ) ^ 2) = (5 : ℝ) := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
    rw [h5_eq] at h2
    rw [h3_eq, h4_eq] at h2
    norm_num at h2 ⊢
    exact h2
  
  exact h5_eq