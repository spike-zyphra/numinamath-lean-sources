import Mathlib

/- Which of the following is the same as

(2−4+6−8+10−12+14)/(3−6+9−12+15−18+21)?
(A) −1  (B)−2/3   (C)2/3 (D)1 (E)14/3-/
theorem algebra_94787 : (2-4+6-8+10-12+14 : ℝ) / (3-6+9-12+15-18+21) = 2 / 3 := by 
    --simply do the calculation 
    field_simp
    norm_num