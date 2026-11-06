import Mathlib

/- Isaac has written down one integer two times and another integer three times. The sum of the five numbers is 100, and one of the numbers is 28. What is the other number?
(A)8(B)11(C)14(D)15(E)18 -/
theorem algebra_96854 (x y : ℤ) (h₀ : x * 2 + y * 3 = 100) (h₁ : y = 28) :
x = 8 := by 
--substitute y in the equation h₀
    rw[h₁] at h₀
    ring_nf at h₀
--solve the resulting equation for x via linear algebra.
    have hk := congrFun (congrArg HAdd.hAdd h₀) (-84)
    ring_nf at hk
    rify at hk
    rify
    have hkk := congrFun (congrArg HMul.hMul hk) (1/2)
    ring_nf at hkk
    exact hkk