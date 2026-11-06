import Mathlib

theorem number_theory_323193 (x y : ℕ) :
    ¬ (∃ n, n^2 = x^2 + y + 1 ∧ ∃ m, m^2 = y^2 + 4 * x + 3) := by
  rintro ⟨n, hn, ⟨m, hm⟩⟩
  have h1 : n > x := by
    by_contra h
    push_neg at h
    have : n ≤ x := by linarith
    have h2 : n^2 ≤ x^2 := by nlinarith [sq_nonneg (x - n : ℤ), sq_nonneg (n : ℕ)]
    nlinarith [hn]
  have h2 : m > y := by
    by_contra h
    push_neg at h
    have : m ≤ y := by linarith
    have h3 : m^2 ≤ y^2 := by nlinarith [sq_nonneg (y - m : ℤ), sq_nonneg (m : ℕ)]
    nlinarith [hm]
  have h3 : n ≤ x + 1 := by
    nlinarith [sq_nonneg (n - (x + 1) : ℤ), sq_nonneg (n - x : ℤ), sq_nonneg (m - (y + 1) : ℤ), sq_nonneg (m - y : ℤ)]
  have h4 : n = x + 1 := by
    nlinarith
  have h5 : y = 2 * x := by 
    rw [h4] at hn
    nlinarith
  rw [h5] at hm
  have h6 : m ≤ 2 * x + 1 := by
    nlinarith [sq_nonneg (m - (2 * x + 1) : ℤ), sq_nonneg (m - (2 * x) : ℤ)]
  have h7 : m ≥ 2 * x + 1 := by
    nlinarith [sq_nonneg (m - (2 * x + 1) : ℤ), sq_nonneg (m - (2 * x) : ℤ)]
  have h8 : m = 2 * x + 1 := by
    linarith
  rw [h8] at hm
  ring_nf at hm
  all_goals
    try { 
      have h9 : x ≤ 1 := by
        nlinarith
      interval_cases x <;> omega 
    }
    <;> try { nlinarith }