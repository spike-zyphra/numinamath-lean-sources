import Mathlib

/- Example 13 (2000 National College Entrance Examination Question) Let $\left\{a_{n}\right\}$ be a sequence of positive terms with the first term being 1, and $(n+1) a_{n+1}^{2}-$ $n a_{n}^{2}+a_{n} a_{n+1}=0(n=1,2,3, \cdots)$, then its general term $a_{n}=$ $\qquad$ . -/
theorem algebra_109290 {a : ℕ → ℝ} (ha : ∀ n ≥ 1, 0 < a n) (h1 : a 1 = 1)
    (h2 : ∀ n ≥ 1, (n + 1) * (a (n + 1)) ^ 2 - n * (a n) ^ 2 + a n * a (n + 1) = 0) :
    ∀ n ≥ 1, a n = 1 / n := by
  rintro n hn
  -- we'll use induction
  induction' n, hn using Nat.le_induction with m hm hm'
  -- for 1 just plug in
  . rw [h1]
    norm_num
  -- assume true for m, we'll prove for m + 1, plug in the equation
  . specialize h2 m (by linarith)
    rw [hm', show (m * (1/m)^2 : ℝ) = 1 / m by field_simp; ring] at h2
    -- factorize to following
    replace h2 : (m + 1) * (a (m + 1) - 1 / (m + 1)) * (a (m + 1) + 1 / m) = 0 := by
      field_simp at h2 ⊢
      linear_combination h2
    -- so one of the 3 multiplicant is 0, first one is positive number, 3rd one implies a(m+1) is negative, somust be 2nd, which proves the goal
    simp at h2
    obtain (h | h) | h := h2
    . linarith
    . ring_nf at h ⊢
      push_cast
      linarith
    . specialize ha (m + 1) (by linarith)
      have : 0 < (m : ℝ)⁻¹ := by positivity
      linarith