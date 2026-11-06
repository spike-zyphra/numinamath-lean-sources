import Mathlib

open Real

/- The remainder can be defined for all real numbers x and y with y≠0 by rem(x,y)=x−y⌊x/y⌋
where ⌊x/y⌋ denotes the greatest integer less than or equal to x/y. What is the value of rem(3/8,−2/5)?
(A)−3/8    (B)−1/40   (C)0    (D)3/8    (E)31/40
-/
theorem algebra_95765 {rem : ℝ → ℝ → ℝ} (hrem : ∀ x y, y ≠ 0 → rem x y = x - y * ⌊x / y⌋) :
rem (3 / 8) (-2 / 5) = -1 / 40 := by
--we check that 3/8 and -2/5 fulfill the hypotheses in hrem and than we use the rem definition 
  norm_num [hrem, Int.floor_eq_iff]