import Mathlib


/- Find the smallest integer value of $n$ such that $n^2-5n-14$ is negative. -/
theorem algebra_21740 : IsLeast {n | n ^ 2 - 5 * n - 14 < 0} (-1) := by
  refine' ⟨by norm_num, fun a h => _⟩
  norm_num at h
  nlinarith