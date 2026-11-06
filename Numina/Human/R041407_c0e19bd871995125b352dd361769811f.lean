import Mathlib

/- 8.16 If \(x\) and \(y\) are both natural numbers, prove that \(x^{2}+y+1\) and \(y^{2}+4 x+3\) cannot both be perfect squares at the same time.
(China Beijing Junior High School Grade 2 Mathematics Competition, 1992)-/
theorem number_theory_284965 (x y : ℕ) :
    ¬(∃ n m, n ^ 2 = x ^ 2 + y + 1 ∧ m ^ 2 = y ^ 2 + 4 * x + 3) := by
  -- Assume on the contrary that there exists such numbers n, m such that n² = x² + y + 1 and m² = y² + 4x + 3.
  intro h
  rcases h with ⟨n, m, hn, hm⟩
  -- First we eliminate the case x = 0.
  by_cases hx : x = 0
  . -- Suppose x = 0.
    simp_all
    by_cases hy : y < 2
    . interval_cases y
      . -- Suppose y = 0, clearly 3 is not a square.
        linarith only [show 1 < m by nlinarith, show m < 2 by nlinarith]
      . -- Suppose y = 1, clearly 2 is not a square.
        linarith only [show 1 < n by nlinarith, show n < 2 by nlinarith]
    . -- Suppose y ≥ 2. Then we have y² < y² + 3 < y² + 2y + 1.
      linarith only [show y < m by nlinarith, show m < y + 1 by nlinarith]
  . replace hx : x ≥ 1 := by
      omega
    by_cases hxy : x ≥ y
    . -- Suppose x ≥ y, then x² < x² + y + 1 < x² + 2x + 1 = (x + 1)².
      linarith only [show x < n by nlinarith, show n < x + 1 by nlinarith]
    . -- Suppose x < y, then y² < y² + 4x + 3 < (y + 2)², so m = y + 1.
      have : m = y + 1 := by
        linarith only [show y < m by nlinarith, show m < y + 2 by nlinarith]
      -- We then have y = 2x + 1, and we substitute in n² = x² + y + 1 to get n² = x² + 2x + 2.
      replace hn : n ^ 2 = x ^ 2 + 2 * x + 2 := by
        linarith only [hn, show y = 2 * x + 1 by nlinarith]
      -- But this is impossible since (x + 1)² < n² < (x + 2)².
      linarith only [show x + 1 < n by nlinarith, show n < x + 2 by nlinarith]