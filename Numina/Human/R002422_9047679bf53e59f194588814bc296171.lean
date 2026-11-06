import Mathlib
import Mathlib.Tactic.NormNum

/--
Mr. Lopez has a choice of two routes to get to work. Route A is 6 miles long,
and his average speed along this route is 30 miles per hour. Route B is 5 miles
long, and his average speed along this route is 40 miles per hour, except for
a 1/2-mile stretch in a school zone where his average speed is 20 miles per
hour. By how many minutes is Route B quicker than Route A?

(A) 2 3/4  
(B) 3 3/4  
(C) 4 1/2  
(D) 5 1/2  
(E) 6 3/4
-/

theorem algebra_93168 :
  let timeA := (6 : ℝ) / 30 
  let timeB := (0.5 : ℝ) / 20 + (4.5 : ℝ) / 40; (timeA - timeB) * 60 = 3.75 := by
    -- Both times A and B follow from the fact that time is distance divided by speed.
    -- `norm_num` confirms that: timeA = 6/30 = 0.2 hours (i.e.,12 minutes), timeB = 0.5/20 + 4.5/40 = 0.1375 hours (in other terms, 8.25 minutes), so the difference of such times is 3.75 minutes.
  norm_num