import Mathlib

/- Three machines P, Q, and R, working together, can do a job in x hours. 
When working alone, P needs an additional 6 hours to do the job; 
Q, one additional hour; and R, x additional hours. The value of x is:
(A) 2/3 (B) 11/12 (C) 3/2 (D) 2 (E) 3 -/

theorem algebra_93151 (x : ℝ) (hx : 0 < x) (h : 1 / x = 1 / (x + 6) + 1 / (x + 1) + 1 / (x + x)) :
x = 2 / 3 := by
--The claim follows from arithmetic calculations on the hypothesis h
  field_simp at h
  ring_nf at h
  nlinarith