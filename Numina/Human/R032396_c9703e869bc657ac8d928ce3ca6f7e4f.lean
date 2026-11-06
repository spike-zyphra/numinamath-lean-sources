import Mathlib

/- The set $\{5, 8, 10, 18, 19, 28, 30, x\}$ has eight members. The mean of the set's members is 4.5 less than $x$. What is the value of $x$ ? -/
theorem algebra_21348 (x : ℝ)
  (h1 : x ≠ 5 ∧ x ≠ 8 ∧ x ≠ 10 ∧ x ≠ 18 ∧ x ≠ 19 ∧ x ≠ 28 ∧ x ≠ 30)
  (h2:(5+8+10+18+19+28+30+x)/8 = x-4.5): x=22 := by
  -- simplify, average is (118+x)/8
  have hh1: (118+x)/8 = x-4.5 := by
    rw [← h2]; norm_num
  -- multiply 8 to the right side, 118+x = 8x-36
  have hh2: 118+x = 8*x-36 := by
    have: 8*x-36 = 8*(x-4.5) := by ring
    rw [this, ← hh1]; ring
  -- therefore 7x = 118+36=154
  have hh3: 7*x = 154 := by
    linarith [hh2]
  -- x = 154/7 = 22
  linarith [hh3]