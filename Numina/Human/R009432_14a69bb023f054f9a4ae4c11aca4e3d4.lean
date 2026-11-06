import Mathlib

/- What are the last 8 digits of

$$
11 \times 101 \times 1001 \times 10001 \times 100001 \times 1000001 \times 111 ?
$$-/
theorem number_theory_608673 : (11 * 101 * 1001 * 10001 * 100001 * 1000001 * 111) % (10 ^ 8) = 19754321 := by
  -- Direct computation.
  norm_num