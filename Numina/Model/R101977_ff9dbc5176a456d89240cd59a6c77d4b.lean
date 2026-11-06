import Mathlib

theorem algebra_243230 (k : ℕ) (hk : k > 0) (h : Real.sqrt 2 + Real.sqrt 8 + Real.sqrt 18 = Real.sqrt k) :
    k = 72 := by
  have h1 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> linarith
  have h2 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  rw [h1, h2] at h
  
  have h3 : Real.sqrt 2 + (2 * Real.sqrt 2) + (3 * Real.sqrt 2) = 6 * Real.sqrt 2 := by
    ring
  
  rw [h3] at h

  have h4 : (6 * Real.sqrt 2) ^ 2 = (k : ℝ) := by
    calc
      (6 * Real.sqrt 2) ^ 2 = (Real.sqrt k) ^ 2 := by rw [h]
      _ = (k : ℝ) := by 
        rw [Real.sq_sqrt]
        have : (k : ℝ) ≥ 0 := by exact_mod_cast show k ≥ 0 by omega
        all_goals norm_num

  have h5 : (6 * Real.sqrt 2) ^ 2 = (72 : ℝ) := by
    calc
      (6 * Real.sqrt 2) ^ 2 = (6 ^ 2 : ℝ) * (Real.sqrt 2)^2 := by ring
      _ = (36 : ℝ) * (Real.sqrt 2^2) := by norm_num
      _ = (36 : ℝ) * (2 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      _ = (72 : ℝ) := by norm_num
  
  have eq1 : (k : ℝ) = (72 : ℝ) := by 
    linarith
  
  have eq2 : k = 72 := by 
    exact_mod_cast eq1
  
  exact eq2