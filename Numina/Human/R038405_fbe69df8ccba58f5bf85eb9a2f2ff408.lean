import Mathlib

/- It is known that, for all positive integers $k$,
$1^2+2^2+3^2+\ldots+k^{2}=\frac{k(k+1)(2k+1)}6$.
Find the smallest positive integer $k$ such that $1^2+2^2+3^2+\ldots+k^2$ is a multiple of $200$.
 -/
theorem number_theory_13782 :
    IsLeast {k : ℕ | 0 < k ∧ 200 ∣ ∑ i in Finset.Icc 1 k, i^2} 112 := by
  refine' ⟨by decide, _⟩
  intro k h
  norm_num at h
  by_contra! hk
  revert h
  revert k
  decide