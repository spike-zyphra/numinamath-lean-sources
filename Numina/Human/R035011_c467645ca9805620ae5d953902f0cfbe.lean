import Mathlib

/- A line with slope 2 intersects a line with slope 6 at the point (40,30). 
What is the distance between the x-intercepts of these two lines?
(A) 5(B) 10(C) 20(D) 25(E) 50 -/
theorem algebra_98282 (x1 x2 y1 y2: ℝ)  (h1 : x1 * 2 = y1) (h2 : x2 * 6 = y2)
(h3 : y1 = 30) (h4 : y2 = 30) :
|x1 - x2| = 10 := by 
--substitute the values of y1 and y2 to find x1 and x2
  rw[h3] at h1
  rw[h4] at h2
--compute x1
  have x : x1 = 15 := by
    rw[mul_comm] at h1
    linarith
--compute x2  
  have x' : x2 = 5 := by
    rw[mul_comm] at h2
    linarith
--compute |x1 - x2| substituting the values of x1 and x2    
  rw[x, x']
  ring_nf
  simp