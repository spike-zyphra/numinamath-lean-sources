import Mathlib

/- Sam drove 96 miles in 90 minutes. His average speed during the first 30
minutes was 60 mph (miles per hour), and his average speed during the second
30 minutes was 65 mph. What was his average speed, in mph, during the last
30 minutes?

(A) 64
(B) 65
(C) 66
(D) 67
(E) 68
-/
theorem algebra_96966 (v : ℝ) (h : v > 0) (h1 : 96 / 1.5 = (60 * 0.5 + 65 * 0.5 + v * 0.5) / (0.5 + 0.5 + 0.5)) :
v = 67 := by
  -- factor out v in hypothesis and calculate
  apply congr_arg (fun x => x * 3 - 125) at h1
  ring_nf at h1
  linarith