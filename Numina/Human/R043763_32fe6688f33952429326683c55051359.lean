import Mathlib

/- When a bucket is two-thirds full of water, the bucket and water weigh a kilograms. 
When the bucket is one-half full of water the total weight is b kilograms. In terms of 
a and b, what is the total weight in kilograms when the bucket is full of water?

(A) (2/3)a + (1/3)b   (B) (3/2)a - (1/2)b   (C) (3/2)a + b   (D) (3/2)a + 2b  (E) 3a − 2b -/

theorem algebra_93892 {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y)
(h1 : x + (2/3) * y = a) (h2 : x + (1/2) * y = b) :
x + y = 3 * a - 2 * b := by
--the conditions h1 and h2 give a system of two equations in 4 indeterminates. 
--Since we have to express the result in terms of a and b the system becomes of two indeterminates, hence solvable by standard arithmetic.
  rw[← h1, ← h2]
  ring