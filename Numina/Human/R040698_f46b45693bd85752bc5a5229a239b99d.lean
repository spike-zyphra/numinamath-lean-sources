import Mathlib

/- Let $a, b, c, d$ be non-negative real numbers whose sum is 1. Prove that


$$

|a b-c d| \leq \frac{1}{4}

$$
 -/
theorem inequalities_216054 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : a + b + c + d = 1) :
    |a * b - c * d| ≤ 1 / 4 := by
  -- assume wlog cd ≤ ab, as since symmetric for absolute value term
  wlog h : c * d ≤ a * b
  . simp at h
    rw [← abs_neg, neg_sub]
    exact this c d a b (by assumption) (by assumption) (by assumption) (by assumption) (by linarith) (by linarith)
  -- so now the lhs is ab - cd
  rw [abs_of_nonneg (by linarith)]
  -- now just use algebraic manipulations and a two variable am-gm application
  calc
    a*b - c*d ≤ a*b - 0 := by gcongr; positivity
    _ ≤ ((a + b)/2)^2 := by linarith [show 0 ≤ (a-b)^2 by positivity]
    _ ≤ ((a + b + c + d)/2)^2 := by
      gcongr (?_/2)^2
      linarith
    _ = 1 / 4 := by
      rw [hsum]
      norm_num