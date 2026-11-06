import Mathlib

/- If ∣x − 2∣ = p, where x < 2, then x − p =
(A) −2
(B) 2
(C) 2−2p
(D) 2p−2
(E) ∣2p−2∣ -/
theorem algebra_93632 (x p : ℝ) (hx : x < 2) (h : abs (x - 2) = p) : x - p = 2 - 2 * p := by
  --when the argument y of the absolute value |y|=k is negative you have -y = k. 
  have hh: x - 2 ≤ 0 := by linarith 
  have hhh: |x - 2| = -(x - 2) := by exact abs_of_nonpos hh
  rw[hhh] at h
  --solve by linear arithmetic the equality to find the result
  linarith