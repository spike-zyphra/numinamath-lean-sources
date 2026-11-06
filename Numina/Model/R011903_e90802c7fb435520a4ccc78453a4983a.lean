import Mathlib

theorem algebra_159987 {a b : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x + b) :
    ¬(|f 0 - 1| < 1 ∧ |f 1 - 3| < 1 ∧ |f 2 - 9| < 1) := by
  by_contra h
  rcases h with ⟨h0, h1, h2⟩
  -- Compute f 0, f 1, f 2
  have h00 : f 0 = b := by 
    rw [hf 0]
    all_goals 
      ring
  -- Compute f 1
  have h01 : f 1 = a + b := by 
    rw [hf 1]
    all_goals 
      ring
  -- Compute f 2
  have h02 : f 2 = 2 * a + b := by 
    rw [hf 2]
    all_goals 
      ring
  -- Convert |f 0 - 1| < 1 into concrete inequalities.
  have h0' : -1 < f 0 - 1 := by linarith [abs_lt.mp h0]
  have h0'' : f 0 - 1 < 1 := by linarith [abs_lt.mp h0]
  -- Convert |f 1 - 3| < 1 into concrete inequalities.
  have h1' : -1 < f 1 - 3 := by linarith [abs_lt.mp h1]
  have h1'' : f 1 - 3 < 1 := by linarith [abs_lt.mp h1]
  -- Convert |f 2 - 9| < 1 into concrete inequalities.
  have h2' : -1 < f 2 - 9 := by linarith [abs_lt.mp h2]
  have h2'' : f 2 - 9 < 1 := by linarith [abs_lt.mp h2]
  -- Derive concrete inequalities |b - 1| < 1
  have h3 : 0 < b := by
    linarith [h0', h00]
  -- Derive concrete inequalities |b - 1| < 1
  have h4 : b < 2 := by
    linarith [h0'', h00]
  -- Derive concrete inequalities |a + b - 3| < 1
  have h5 : 2 < a + b := by
    linarith [h1', h01]
  -- Derive concrete inequalities |a + b - 3| < 1
  have h6 : a + b < 4 := by
    linarith [h1'', h01]
  -- Derive concrete inequalities |2a + b - 9| < 1
  have h7 : 8 < 2 * a + b := by
    linarith [h2', h02]
  -- Derive concrete inequalities |2a + b - 9| < 1
  have h8 : 2 * a + b < 10 := by
    linarith [h2'', h02]
  -- Derive contradictions here
  -- From h7 and h6: 8 < 2a + b and a + b < 4.
  -- Subtract to get 8 - 4 < a, which simplifies to 4 < a
  have h9 : 4 < a := by
    nlinarith
  -- From h6 and h3: a + b < 4 and 0 < b.
  -- Subtract to get a < 4 - b < 4 (since b > 0)
  have h10 : a < 4 := by
    nlinarith
  -- Now we have 4 < a < 4, which is a contradiction.
  linarith