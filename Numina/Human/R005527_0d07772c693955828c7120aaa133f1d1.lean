import Mathlib
open Real


/-
If $A=10^{9}-987654321$ and $B=\frac{123456789+1}{10}$, what is the value of $\sqrt{A B}$ ?
-/
theorem algebra_608667 (ha: A = 10^9 - 987654321) (hb: B = (123456789+1)/10) : sqrt (A * B) = 12345679 := by
  
  -- Cacuclating A=12345679
  have ha1: A = 12345679 := by
    calc
      A = 10^9 - 987654321 := by  rw [ha]
      _ = 1000000000 - 987654321 := by linarith
      _ = 12345679 := by ring_nf
    
  -- Calculating B=12345679
  have hb1: B = 12345679 := by
    calc
      B = (123456789+1)/10 := by rw[hb]
      _ = 123456790/10 := by linarith
      _ = 12345679 := by ring_nf
  rw [ha1, hb1]

  -- Take square root on both sides
  field_simp
      