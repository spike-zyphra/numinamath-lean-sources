import Mathlib

/- Lucky Larry's teacher asked him to substitute numbers for a, b, c, d, and e in the expression a−(b−(c−(d+e))) and evaluate the result. 
Larry ignored the parenthese but added and subtracted correctly and obtained the correct result by coincidence. The number Larry substituted for a, b, c, and d were 1, 2, 3, and 4, respectively. What number did Larry substitute for e?
(A) −5(B) −3(C) 0(D) 3(E) 5 -/
theorem algebra_94434 {a b c d e : ℤ} (ha : a = 1) (hb : b = 2) (hc : c = 3) (hd : d = 4)
(h : a - (b - (c - (d + e))) = a - b - c - d + e) :
e = 3 := by 
    --we substitute the numbers a, b, c and d
    rw[ha, hb, hc, hd] at h
    --compute the algebraic expression solving for e
    ring_nf at h
    have h2 := congrFun (congrArg HAdd.hAdd h) (e+8)
    ring_nf at h2
    rify at h2
    rify
    have h3 := congrFun (congrArg HMul.hMul h2) (1/2)
    simp at h3
    ring_nf at h3
    rw[h3]