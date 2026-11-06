import Mathlib
open Mathlib
/--
A football game was played between two teams, the Cougars and the Panthers.  The two teams scored a total of 34 points, and the Cougars won by a margin of 14 points.  How many points did the Panthers score?
$\text {(A) } 10 \qquad \text {(B) } 14 \qquad \text {(C) } 17 \qquad \text {(D) } 20 \qquad \text {(E) } 24$
-/
lemma algebra_1173 (cougars panthers : ℕ) (h1 : cougars + panthers = 34) (h2 : cougars = panthers + 14) : panthers = 10 := by
  -- panthers + 14 + panthers = 34
  rw [h2] at h1
  -- 2 * panthers + 14 = 34
  have as : 2 * panthers + 14 = 34 := by omega
  -- 2 * panthers = 20
  have sl : 2 * panthers = 20 := by omega
  -- panthers = 10
  omega