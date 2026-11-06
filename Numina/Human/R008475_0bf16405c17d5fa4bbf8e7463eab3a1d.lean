import Mathlib

/- Suppose that the number a satisfies the equation 4 = a + a^−1. What is the value of a^4 + a^−4?
(A) 164(B) 172(C) 192(D) 194(E) 212 -/
theorem algebra_96704 {a : ℝ} (ha : a ≠ 0) (h : 4 = a + 1 / a) :
a ^ 4 + 1 / a ^ 4 = 194 := by
--calculate first a^2 + 1/a ^2 by using the relation h
  have h₁ : a ^ 2 + 1 / a ^ 2 = 14 := by
    field_simp at h ⊢
    nlinarith
--use the relation h₁ into the claim to conclude 
  field_simp at h₁ ⊢
  nlinarith