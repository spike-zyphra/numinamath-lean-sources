import Mathlib

open Matrix

theorem calculus_13129 (f : Matrix (Fin 2) (Fin 2) ℝ) (hf : ∀ i j, i = 0 → j = 0 → f i j = 1) (hf' : ∀ i j, i = 0 → j ≠ 0 → f i j = 0) (hf'' : ∀ i j, i ≠ 0 → j = 0 → f i j = 0) (hf''' : ∀ i j, i ≠ 0 → j ≠ 0 → f i j = -1) : f = !![1, 0; 0, -1] := by
  have f00 : f 0 0 = 1 := hf 0 0 (by simp) (by simp)
  have f01 : f 0 1 = 0 := hf' 0 1 (by simp) (by simp)
  have f10 : f 1 0 = 0 := hf'' 1 0 (by simp) (by simp)
  have f11 : f 1 1 = -1 := hf''' 1 1 (by simp) (by simp)
  funext i j 
  fin_cases i <;> fin_cases j <;> simp [f00, f01, f10, f11] at *
  <;> try { tauto }
  <;> try { linarith }