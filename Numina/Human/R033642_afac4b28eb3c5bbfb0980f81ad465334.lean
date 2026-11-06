import Mathlib
import Mathlib.Tactic.NormNum

/--
The ratio of the measures of two acute angles is 5:4, and the complement of one
of these two angles is twice as large as the complement of the other. What is the sum of the degree measures of the two angles?

(A) 75  
(B) 90  
(C) 135  
(D) 150  
(E) 270
-/

theorem algebra_96035 :
    --We use the following reasoning: First, we let the angles be 5k and 4k, both less than 90°. The condition "the complement of one is twice the complement of the other"   translates to: `90 - (4k) = 2 * (90 - 5k)`. Solving yields `k = 15`, hence the angles are 75° and 60°, whose sum is 135°.
    --Here we define k=15, A=5k=75, B=4k=60.
  let k := (15 : ℝ)
  let A := 5 * k
  let B := 4 * k
    --So, we check the condition 90 - B = 2 * (90 - A) => 90 - 60= 2(90 - 75) => 30=2*15 => 30=30
  90 - B = 2 * (90 - A) := by norm_num