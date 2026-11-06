import Mathlib

theorem algebra_994 {a b c : ℝ} (h1 : 3*a+7*b+c=3.15) (h2 : 4*a+10*b+c=4.20) :
    a+b+c=1.05 := by
  ring_nf at h1 h2 ⊢ 
  linarith