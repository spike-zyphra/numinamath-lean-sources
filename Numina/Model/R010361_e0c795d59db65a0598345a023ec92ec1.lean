import Mathlib

theorem algebra_607892 (a b c d : ℤ) (ha : a ≥ b) (hb : b ≥ c) (hc : c ≥ d) (hd : d > 0) : ¬(∃ m : ℤ, m ^ 4 - a * m ^ 3 - b * m ^ 2 - c * m - d = 0) := by
  -- Proof by contradiction
  by_contra H
  rcases H with ⟨m, hm⟩
  -- First prove m ≠ 0 since if m = 0, then -d = 0 contradicts d > 0
  have h1 : m ≠ 0:= by
    by_contra H
    subst m
    simp at hm
    omega
  -- Since m ≠ 0, m must be either positive or negative
  replace h1 : m > 0 ∨ m < 0:= by exact Int.ne_iff_lt_or_gt.mp (id (Ne.symm h1))
  rcases h1 with h1 | h1
  . -- Case 1: m > 0
    -- Prove m > a by manipulating the equation
    have h2 : m > a:= by
      replace hm : (m - a) * m ^ 3 = b * m ^ 2 + c * m + d:= by linarith
      replace hm : (m - a) * m ^ 3 > 0:= by
        rw [hm]
        have hb : b > 0:= by linarith
        have hc : c > 0:= by linarith
        positivity
      have h3 : m ^ 3 > 0:= by positivity
      replace hm : m - a > 0:= by exact (pos_iff_pos_of_mul_pos hm).mpr h3
      linarith
    -- Prove m^3 - a*m^2 - b*m - c ≥ 1
    have h3 : m ^ 3 - a * m ^ 2 - b * m - c ≥ 1:= by
      nlinarith
    -- Multiply by m and derive contradiction
    have h4 : m ^ 4 - a * m ^ 3 - b * m ^ 2 - c * m ≥ m:= by
      nlinarith
    linarith
  . -- Case 2: m < 0
    -- Handle the negative case
    have h2 : m ≤ -1:= by omega
    -- Prove that m^4 ≤ ... to derive a contradiction with positivity of a term
    nlinarith [sq_nonneg (m ^ 2 - 1), sq_nonneg (m - 1), sq_nonneg (m ^ 2 - m), sq_nonneg (m + 1), sq_nonneg (m ^ 2 + 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d)]