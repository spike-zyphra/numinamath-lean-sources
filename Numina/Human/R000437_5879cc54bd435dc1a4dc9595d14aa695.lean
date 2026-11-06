import Mathlib

open Real

/- Given that $A = (\sqrt{2008}+\sqrt{2009}),$ $B = (-\sqrt{2008}-\sqrt{2009}),$ $C = (\sqrt{2008}-\sqrt{2009}),$ and $D = (\sqrt{2009}-\sqrt{2008}),$ find $ABCD.$ -/
theorem algebra_10557 {A B C D : ℝ}
    (hA : A = sqrt 2008 + sqrt 2009)
    (hB : B = -sqrt 2008 - sqrt 2009)
    (hC : C = sqrt 2008 - sqrt 2009)
    (hD : D = sqrt 2009 - sqrt 2008) :
    A * B * C * D = 1 := by 
  rw [hA, hB, hC, hD]
  ring_nf
  nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2008 from by norm_num),
    sq_sqrt (show (0 : ℝ) ≤ 2009 from by norm_num)]