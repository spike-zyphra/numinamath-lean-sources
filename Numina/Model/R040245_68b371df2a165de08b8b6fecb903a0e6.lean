import Mathlib

theorem algebra_175467 (t : ℤ) :
    (∃ n, (4*t)^2 + (3-2*t-t^2)^2 + (3+2*t-t^2)^2 = 2*n^2) ∧
    ∃ m, (4*t)^4 + (3-2*t-t^2)^4 + (3+2*t-t^2)^4 = 2*m^4 := by
  constructor 
  · -- Show that the sum of squares is twice a square
    use t ^ 2 + 3 
    ring_nf 
  · -- Show that the sum of fourth powers is twice a fourth power 
    use (t ^ 2 + 3) 
    ring_nf