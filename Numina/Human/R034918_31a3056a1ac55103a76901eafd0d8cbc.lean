import Mathlib

/- Let a,b,c,d, and e be five consecutive terms in an arithmetic sequence, and suppose that a+b+c+d+e=30. Which of a,b,c,d, or e can be found?
(A) a(B) b(C) c(D) d(E) e -/
theorem algebra_98239 (a b c d e k : ℤ) (hb : b = a + k) (hc : c = b + k) (hd : d = c + k) (he : e = d + k) (h: a + b + c + d + e = 30) :
c = 6 := by
    --substitute b, c, d and e in terms of a
    rify at hb hc hd he h
    rw[he, hd, hc, hb] at h
    --simplify the expression to get a+2k=6
    ring_nf at h
    have hk := congrFun (congrArg HMul.hMul h) (1/5:ℝ)
    ring_nf at hk
    --find c= a+2k
    rw[hb] at hc
    ring_nf at hc
    --conclude rewriting by transitive property
    rw[hk] at hc
    rify
    exact hc