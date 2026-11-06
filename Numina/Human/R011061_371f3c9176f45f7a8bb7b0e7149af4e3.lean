import Mathlib

/- Teams A and B are playing in a basketball league where each game results in a win for one team and a loss for the other team. 
Team A has won 2/3 of its games and team B has won 5/8 of its games. 
Also, team B has won 7 more games and lost 7 more games than team A. 
How many games has team A played?
(A) 21
(B) 27
(C) 42
(D) 48
(E) 63 -/
theorem algebra_93937 {a b : ℕ} (ha : a > 0) (hb : b > 0)
(h1 : (2 / 3 : ℚ) * a = (5 / 8 : ℚ) * b - 7) (h2 : (1 / 3 : ℚ) * a = (3 / 8 : ℚ) * b - 7) :
a = 42 := by
  --solve the linear system with indeterminates a and b
  field_simp at h1 h2
  --first find b
  have h2' := congrFun (congrArg HMul.hMul h2) (2)
  ring_nf at h1 h2'
  rw[h2'] at h1
  have h : (b : ℚ) = 56 := by linarith
  --substitute b in the other equation and find a
  rw[h] at h2'
  have h' : (a : ℚ) = 42 := by linarith
  qify
  exact h'