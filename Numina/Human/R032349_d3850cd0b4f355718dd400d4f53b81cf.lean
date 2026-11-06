import Mathlib

/- The equations 2x+7=3 and bx−10=−2 have the same solution. What is the value of b?
(A)−8(B)−4(C) 2(D) 4(E) 8 -/
theorem algebra_95745 {x b : ℝ} (h₁ : 2 * x + 7 = 3) (h₂ : b * x - 10 = - 2) :
b = -4 := by
    --we have a system of two equations in two indeterminates b and x.
    --we solve the first equation given by h₁ for x.
    ring_nf at h₁
    have h := congrFun (congrArg HAdd.hAdd h₁) (-7)
    ring_nf at h
    have hh := congrFun (congrArg HMul.hMul h) (1/2)
    simp at hh
    ring_nf at hh
    --we substitute it in the second equation h₂ and solve for b.
    rw[hh] at h₂
    have k := congrFun (congrArg HAdd.hAdd h₂) (10)
    have kk := congrFun (congrArg HMul.hMul k) (-1)
    ring_nf at kk
    have kkk := congrFun (congrArg HMul.hMul kk) (1/2)
    simp at kkk
    ring_nf at kkk
    exact kkk