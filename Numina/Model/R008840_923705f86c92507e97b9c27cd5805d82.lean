import Mathlib

theorem algebra_10243 {n : ℕ} (h : n * (n + 1) = 18360) : n + (n + 1) = 271 := by
  have h1 : n ≤ 136 := by
    nlinarith [h, sq_nonneg (n - 135 : ℤ), sq_nonneg (n + 136 : ℤ)]
  have h2 : n ≥ 135 := by
    nlinarith [h, sq_nonneg (n - 135 : ℤ), sq_nonneg (n + 136 : ℤ)]
  interval_cases n <;> all_goals ring_nf at h ⊢ <;> try { contradiction } <;> omega
  -- wanted h3 : n = 135 := by interval_cases ... so that omega works
  all_goals omega
  <;> try { all_goals tauto }
  <;> try { contradiction }
  <;> try { omega }
  all_goals try { tauto }