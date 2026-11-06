import Mathlib

/- A well-known rule used to find the square of an integer with decimal expansion
  \((a_{n-1} \ldots a_{1} a_{0})_{10}\) where the final digit \(a_{0}=5\) is to calculate the decimal expansion
  of the product \((a_{n} a_{n-1} \ldots a_{1})_{10} \left[\left(a_{n} a_{n-1} \ldots a_{1}\right)_{10}+1\right]\)
  and then append the digits \((25)_{10}\) to the result.

  For example, when calculating \((165)^{2}\), we find that the decimal expansion begins
  with \(16 \cdot 17 = 272\), leading to the conclusion that \((165)^{2} = 27225\).
  We need to demonstrate that this rule is valid. -/
theorem number_theory_4477 (k : ℕ) : (10 * k + 5) ^ 2 = 100 * k * (k + 1) + 25 := by ring
