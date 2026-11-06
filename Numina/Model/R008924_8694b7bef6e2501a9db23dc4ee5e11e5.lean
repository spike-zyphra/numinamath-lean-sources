import Mathlib

theorem algebra_19346 {f : ℝ → ℝ} (hf : f = fun x => 2 ^ x) :
    Real.sqrt (f (f (f (f 1)))) = 256 := by 
  have f1 : f 1 = (2 : ℝ) := by 
    rw [hf]
    norm_num
  have f2 : f (f 1) = (4 : ℝ) := by 
    rw [f1]
    rw [hf]
    norm_num
  have f4 : f (f (f 1)) = (16 : ℝ) := by 
    rw [f2]
    rw [hf]
    norm_num
  have f16 : f (f (f (f 1))) = (65536 : ℝ) := by 
    rw [f4]
    rw [hf]
    norm_num
  rw [f16]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num