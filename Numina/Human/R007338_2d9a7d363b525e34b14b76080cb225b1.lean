import Mathlib

def diamond (x y : ℝ) := |x - y|

/- Define x⋄y to be ∣x−y∣ for all real numbers x and y. What is the value of (1⋄(2⋄3))−((1⋄2)⋄3)?
(A) −2(B) −1(C) 0(D) 1(E) 2 -/
theorem algebra_93849 : (diamond 1 (diamond 2 3)) - diamond (diamond 1 2) 3 = -2 := by 
--we solve the claimed equivalence by using the definiton of the diamond operation and using linear algebra and definition of absolute value.
    unfold diamond
    ring_nf
    simp
    ring_nf
    simp