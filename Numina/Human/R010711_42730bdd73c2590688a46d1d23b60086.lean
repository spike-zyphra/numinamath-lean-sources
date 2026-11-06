import Mathlib
open Mathlib
/--
What is the difference between the sum of the first $2003$ even counting numbers and the sum of the first $2003$ odd counting numbers? 
$\mathrm{(A) \ } 0\qquad \mathrm{(B) \ } 1\qquad \mathrm{(C) \ } 2\qquad \mathrm{(D) \ } 2003\qquad \mathrm{(E) \ } 4006$
-/
lemma algebra_1141 : (∑ k in Finset.range 2003, 2 * (k + 1)) - (∑ k in Finset.range 2003, (2 * k + 1)) = 2003 := by
  native_decide