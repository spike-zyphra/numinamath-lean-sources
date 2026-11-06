import Mathlib

/- The smallest product one could obtain by multiplying two numbers in the set {−7,−5,−1,1,3} is
(A) −35(B) −21(C) −15(D) −1(E) 3 -/
theorem algebra_96714 (s ss : Finset ℤ) (hs : s ={-7, -5, -1, 1, 3}) 
(hss : ss = {x : ℤ | ∃ a : s , ∃ b : s , x = a * b}) :
IsLeast (ss) (-21) := by
  unfold IsLeast
  constructor
---21 is in the set of products of elements of s
  · rw[hss]
    simp
    --7 is in s
    use -7
    constructor
    · rw[hs]
      simp
    --3 is in s
    · use 3
      constructor
      · rw[hs]
        simp
      · ring
--21 is the lower bound in the set of products of elements of s
  · unfold lowerBounds
    rw[hss]
    simp
    intro a x hx y hy hprod
    rw[hprod]
    rw[hs] at hx hy
    --case take all couple of numbers in s and check that 21 is the minimum
    fin_cases hx <;> fin_cases hy <;> norm_num