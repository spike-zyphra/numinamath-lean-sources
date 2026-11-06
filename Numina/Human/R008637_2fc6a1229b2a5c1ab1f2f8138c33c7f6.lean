import Mathlib
open Real

/- The sequence S1, S2, S3, ... , S10 has the property that every term beginning with the third is the sum of the previous two. That is, Sn = Sn-2 + Sn-1 for n ≥ 3. Suppose that S9 = 110 and S7 = 42. What is S4?
(A) 4 (B) 6  (C) 10 (D) 12  (E) 16 -/
theorem algebra_95691 {S : ℕ → ℤ} (hS : ∀ n, S (n + 2) = S n + S (n + 1)) (hS9 : S 9 = 110) (hS7 : S 7 = 42) :
S 4 = 10 := by
  -- unfold the terms and then the question becomes trivial
  simp_all
  linarith