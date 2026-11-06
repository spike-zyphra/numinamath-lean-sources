import Mathlib

open Real

theorem algebra_12669 {f : ℝ → ℝ} (hf : f = fun x => if x < 0 then 0 else (if x = 0 then Real.pi else (x + 1))) :
    f (f (f (-1))) = Real.pi + 1 := by 
  have h1 : f (-1) = 0 := by 
    rw [hf]
    norm_num
  have h2 : f (f (-1)) = Real.pi := by 
    rw [h1]
    rw [hf]
    norm_num
  rw [h2]
  rw [hf]
  have h_pos : Real.pi > (0 : ℝ) := Real.pi_pos
  simp [h_pos, show ¬Real.pi < (0 : ℝ) by linarith, show ¬Real.pi = (0 : ℝ) by linarith]
  <;> linarith