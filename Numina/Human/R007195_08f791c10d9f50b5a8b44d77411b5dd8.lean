import Mathlib

/- What is (1+3+5)/(2+4+6) − (2+4+6)/(1+3+5)?
(A) −1  (B) 5/36    (C) 7/12    (D) 147/60  (E) 43/3 -/
theorem algebra_94748 : (2+4+6 : ℝ)/(1+3+5) - (1+3+5)/(2+4+6) = 7/12 := by
    --solve with algebra calculations
    ring_nf