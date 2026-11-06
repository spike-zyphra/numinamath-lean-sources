import Mathlib

/- A box 2 centimeters high, 3 centimeters wide, and 5 centimeters long can hold 40 grams of clay.  A second box with twice the height, three times the width, and the same length as the first box can hold n grams of clay.  What is n?
(A) 120(B) 160(C) 200(D) 240(E) 280 -/
theorem algebra_95182 (h w l k : ℝ) (h₀ : h = 2) (h₁ : w = 3) (h₂ : l = 5)
(h₃ : 40 = k * h * w * l) (n : ℝ) (hn : n = k * (2 * h) * (3 * w) * l) :
n = 240 := by
    --substitute hight, width and length to get the coefficent of clay holded per unit volume.
    rw[h₀,h₁,h₂] at h₃
    ring_nf at h₃
    have hk := congrFun (congrArg HMul.hMul h₃) (1/30)
    ring_nf at hk
    --substitute  hight with and length again in the proportions of the new box and multiply by the coefficient to get how much clay it can hold.
    rw[←hk, h₀, h₁, h₂] at hn
    --solve the equation algebraically for n
    linarith