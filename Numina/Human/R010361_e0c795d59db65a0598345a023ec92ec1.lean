import Mathlib

/- Let $a, b, c, d$ be positive integers such that $a \geq b \geq c \geq d$. Prove that the equation $x^{4}-a x^{3}-b x^{2}-c x-d=0$ has no integer solution. -/
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
    -- Prove m > a by rearranging the equation
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
    -- Prove m^3 - am^2 - bm - c ≥ 1
    have h3 : m ^ 3 - a * m ^ 2 - b * m - c ≥ 1:= by
      rw [show m ^ 3 - a * m ^ 2 = (m - a) * m ^ 2 by linarith]
      have h3 : m - a ≥ 1:= by omega
      have h4 : m ^ 2 ≥ 0:= by positivity
      replace h3 : (m - a) * m ^ 2 ≥ 1 * m ^ 2:= by exact Int.mul_le_mul_of_nonneg_right h3 h4
      simp at h3
      replace h2 : m - b ≥ 1:= by linarith
      have h5 : (m - b) * m ≥ 1 * m:= by exact Int.mul_le_mul_of_nonneg_right h2 (by omega)
      simp at h2
      linarith
    -- Derive contradiction using d = m(m^3 - am^2 - bm - c)
    replace hm : d = m * (m ^ 3 - a * m ^ 2 - b * m - c):= by linarith
    replace h3 : m * (m ^ 3 - a * m ^ 2 - b * m - c) ≥ m * 1:= (mul_le_mul_iff_of_pos_left h1).mpr h3
    linarith
  . -- Case 2: m < 0
    -- Let n = -m and rewrite equation in terms of n
    set n:= -m with hn
    clear_value n
    replace hn : m = -n:= by linarith
    rw [hn] at hm
    replace h1 : n > 0:= by linarith
    ring_nf at hm
    -- Prove various inequalities to derive contradiction
    have g1 : n ^ 4 > 0:= by positivity
    replace h1 : n ≥ 1:= by linarith
    have g2 : a * n ≥ a * 1:= by exact Int.mul_le_mul_of_nonneg_left h1 (by linarith)
    replace g2 : a * n - b ≥ 0:= by linarith
    replace g2 : n ^ 2 * (a * n - b) ≥ 0:= by positivity
    have g3 : c * n ≥ c * 1:= by exact Int.mul_le_mul_of_nonneg_left h1 (by linarith)
    replace g3 : c * n - d ≥ 0:= by linarith
    linarith
