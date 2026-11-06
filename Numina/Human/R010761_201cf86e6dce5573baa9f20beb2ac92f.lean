import Mathlib

/- Notice that  \[31\cdot37=1147.\]Find some integer $n$ with $0\leq n<2293$ such that  \[31n\equiv 3\pmod{2293}.\] -/
theorem number_theory_23123 : ∃ n, 0 ≤ n ∧ n < 2293 ∧ 31 * n ≡ 3 [ZMOD 2293] := by
  use 222
  norm_num
  exact rfl