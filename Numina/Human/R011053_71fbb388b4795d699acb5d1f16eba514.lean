import Mathlib

/- The weight of 1/3 of a large pizza together with 
3*1/2 cups of orange slices is the same as the weight of 
3/4 of a large pizza together with 1/2 cup of orange slices. A cup of orange slices weighs 1/4 of a pound. What is the weight, in pounds, of a large pizza?
(A) 1*4/5   (B) 2   (C) 2*2/5   (D) 3   (E) 3*3/5-/
theorem algebra_94321 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
(h : (1 / 3) * x + (3 + 1 / 2) * y = (3 / 4) * x + (1 / 2) * y)
(h' : y = (1 / 4)) :
x = 1 + 4 / 5 := by 
    --substitute the value of y in the hypotheses h and solve with linear algebra.
    rw[h'] at h
    field_simp at h
    ring_nf at h
    linarith