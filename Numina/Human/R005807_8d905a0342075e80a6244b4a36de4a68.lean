import Mathlib
/- Let $r=H_{1}$ be the answer to this problem. Given that $r$ is a nonzero real number, what is the value of $r^{4}+4 r^{3}+6 r^{2}+4 r$ ? -/
theorem algebra_610005 (r : ℝ) (hr : r ≠ 0) (h : r ^ 4 + 4 * r ^ 3 + 6 * r ^ 2 + 4 * r = r) : r = -1:= by
  replace h : (r + 1) * (r * ((r + 1) ^ 2 + (r + 2) ^ 2 + 1)) = 0:= by linarith
  simp [hr] at h
  rcases h with h | h
  .
    linarith
  .
    have h1 : (r + 1) ^ 2 + (r + 2) ^ 2 + 1 > 0:= by positivity
    by_contra _
    linarith
  
