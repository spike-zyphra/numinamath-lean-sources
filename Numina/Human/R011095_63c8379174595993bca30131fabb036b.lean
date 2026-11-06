import Mathlib

/- It takes Anna 30 minutes to walk uphill 1 km from her home to school, but it takes her only 10 minutes to walk from school to her home along the same route. What is her average speed, in km/hr, for the round trip?
(A) 3(B) 3.125(C) 3.5(D) 4(E) 4.5 -/
theorem algebra_94725 (d t1 t2 : ℝ) (ht1 : t1 = 30 / 60) (ht2 : t2 = 10 / 60)
(hd : d = 1) :
(2 * d) / (t1 + t2) = 3 := by 
    --substitute the data in the equation
    rw[ht1, ht2, hd]
    --solve the algebraic calculations
    field_simp
    ring