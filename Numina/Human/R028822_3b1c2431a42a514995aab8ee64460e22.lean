import Mathlib

def S : ℕ → ℤ
| n => ∑ i in Finset.range n, (-1 : ℤ)^i * (i + 1)

/- Let S = 1 − 2 + 3 − 4 + ⋯ + (−1)^(n−1) * n, where n=1,2,⋯. 
Then S_17 + S_33 + S_50 equals:
(A) 0(B) 1(C) 2(D) −1(E) −2 -/
theorem algebra_95631 : S 17 + S 33 + S 50 = 1 := by
--the result comes from arithmetic calculation on the function S after subtitution of the values 17, 33 and 50.
rfl