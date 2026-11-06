import Mathlib
/- Carlos went to a sports store to buy running shoes. Running shoes were on sale, with prices reduced by 20% on every pair of shoes. 
Carlos also knew that he had to pay a 7.5% sales tax on the discounted price. He had
43$ dollars. What is the original (before discount) price of the most expensive shoes he could afford to buy? 
(A)$ 46 (B) $50 (C) $48 (D)$47 (E) $49 -/ 
theorem algebra_94620 {x : ℝ} (hx : x ≠ 0) (h : (1 - 20 / 100) * (1 + 7.5 / 100) * x = 43) : x = 50 := by
    --suffices to solve the equation in hypotheis h for x using linear arithmetic procedures.
    field_simp at h
    ring_nf at h
    have hk := congrFun (congrArg HMul.hMul h) (1/8600)
    simp at hk
    ring_nf at hk
    exact hk