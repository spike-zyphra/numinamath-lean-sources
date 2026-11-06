import Mathlib

/- Mrs. Jones is pouring orange juice into four identical glasses for her four sons. She fills the first three glasses completely but runs out of juice when the fourth glass is only 1/3 full. 
What fraction of a glass must Mrs. Jones pour from each of the first three glasses into the fourth glass so that all four glasses will have the same amount of juice?
(A) 1/12    (B)1/4  (C)1/6  (D)1/8  (E)2/9 -/
theorem algebra_94494 (x : ℝ) (hx : x ≠ 0) (h : (3 + 1 / 3) / 4  = (1 - x) ) :
x = 1 / 6 := by
--solve the equation h  by slgebraic manipulations. Notice that the equation tells us that 3 glasses + 1/3 divided by 4 is the amount of water there should be in each one of the glasses. Then the amount of water you take out of each full glass is exactly 1 minus the quantity found. 
    have h1 := congrFun (congrArg HMul.hMul h) (4)
    ring_nf at h1
    have h2 := congrFun (congrArg HAdd.hAdd h1) (-4)
    ring_nf at h2
    have h3 := congrFun (congrArg HMul.hMul h2) (-1/4)
    field_simp at h3
    ring_nf at h3
    have h4 := congrFun (congrArg HMul.hMul h3) (1/12)
    ring_nf at h4
    rw[h4]