import Mathlib

def nabla (a b : ℕ) := 2 + b ^ a

theorem algebra_16604 : nabla (nabla 1 2) 3 = 83 := by 
  unfold nabla
  <;> norm_num