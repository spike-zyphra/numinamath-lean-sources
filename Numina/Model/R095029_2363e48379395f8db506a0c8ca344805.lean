import Mathlib

def nabla (x y z w : ℤ) := x * z + y * w

theorem algebra_263619 : nabla 3 1 4 2 = 14 := by 
  unfold nabla
  norm_num