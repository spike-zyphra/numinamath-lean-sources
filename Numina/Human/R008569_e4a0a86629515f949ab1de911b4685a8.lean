import Mathlib

/- Find $24^{-1} \pmod{11^2}$. That is, find the residue $b$ for which $24b \equiv 1\pmod{11^2}$.

Express your answer as an integer from $0$ to $11^2-1$, inclusive. -/
theorem number_theory_23249 : 24 * 116 ≡ 1 [ZMOD 11 ^ 2] := by
  -- Directly substitute the answer into the question.
  simp [Int.ModEq]
