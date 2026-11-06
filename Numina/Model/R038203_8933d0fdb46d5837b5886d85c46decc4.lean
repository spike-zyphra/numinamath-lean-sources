import Mathlib

theorem number_theory_4182 (a : ℕ) (ha : a > 0) (h1 : ∃ x, x^2 = a + 32) (h2 : ∃ y, y^2 = a + 84) :
    a = 112 := by
  rcases h1 with ⟨x, hx⟩
  rcases h2 with ⟨y, hy⟩

  have eq3 : y^2 = x^2 + 52 := by
    nlinarith

  have eq4 : y > x := by
    by_contra h
    push_neg at h
    have h3 : y ≤ x := by linarith
    have h4 : y^2 ≤ x^2 := by nlinarith [h3, sq_nonneg (x - y)]
    nlinarith
  -- Now, we will find $x$ and $y$.
  -- From `eq3 : y ^ 2 = x ^ 2 + 52`.
  have h3 : y ≤ 32 := by
    nlinarith [sq_nonneg (y - 14 : ℕ), sq_nonneg (x - 12 : ℕ)]
  have h4 : x ≤ 27 := by
    nlinarith [sq_nonneg (y - 14 : ℕ), sq_nonneg (x - 12 : ℕ)]
  interval_cases x <;> try { 
    interval_cases y <;> omega 
    <;> try {nlinarith}
    <;> try { contradiction }
  }
  <;> try { 
    interval_cases y <;> omega 
    <;> try {nlinarith}
    <;> try { contradiction }
  }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try {nlinarith}