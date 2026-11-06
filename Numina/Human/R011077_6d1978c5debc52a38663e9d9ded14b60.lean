import Mathlib

/- LeRoy and Bernardo went on a week-long trip together and agreed to share the costs equally. Over the week, each of them paid for various joint expenses such as gasoline and car rental. At the end of the trip it turned out that LeRoy had paid A dollars and Bernardo had paid B dollars, where A < B. How many dollars must LeRoy give to Bernardo so that they share the costs equally?
(A)(A+B)/2  (B)(A−B)/2  (C)(B−A)/2  (D)B−A  (E)A+B-/
theorem algebra_94939 (A B : ℝ) (hA : A < B) :
(B - A) / 2 = (A + B) / 2 - A := by 
    --it suffices to solve using linear arithmetic the expression given
    linarith