import Mathlib

/- In the eight term sequence A, B, C, D, E, F, G, H, the value of C is 5 and the sum of any three consecutive terms is 30. What is A+H?
(A) 17(B) 18(C) 25(D) 26(E) 43 -/
theorem algebra_92937 {A B C D E F G H : ℝ}
(hC : C = 5) (hsum : A + B + C = 30 ∧ B + C + D = 30 ∧ C + D + E = 30 ∧ D + E + F = 30 ∧ E + F + G = 30 ∧ F + G + H = 30) :
A + H = 25 := by 
    --divide the informations in the hypotheses hsum
    obtain ⟨h1,h2,h3,h4,h5, h6 ⟩:= hsum 
    --substitute the value of B+C in the second equation
    have k1 := congrFun (congrArg HAdd.hAdd h1) (-A)
    ring_nf at k1
    rw[k1] at h2
    --substitute D=A in the fourth equation
    have k2 := congrFun (congrArg HAdd.hAdd h2) (A-30)
    ring_nf at k2
    rw[k2] at h4
    --substitute E+F in the fifth equation
    have k4 := congrFun (congrArg HAdd.hAdd h4) (-A)
    ring_nf at k4
    rw[k4] at h5
    --substitute G=A un the sixth equation
    have k5 := congrFun (congrArg HAdd.hAdd h5) (A-30)
    ring_nf at k5
    rw[k5] at h6
    --use C=5 and D=A in the third equation and substitute A+E in the fourth equation
    rw[k2,hC] at h3
    have k3 := congrFun (congrArg HAdd.hAdd h3) (-A-5)
    ring_nf at k3
    --then you get F in numbers
    rw[k3] at h4
    ring_nf at h4
    have j4 := congrFun (congrArg HAdd.hAdd h4) (-25)
    ring_nf at j4
    --substitute f in the sixth equation and solve for A+H
    rw[j4] at h6
    have k6 := congrFun (congrArg HAdd.hAdd h6) (-5)
    ring_nf at k6
    exact k6