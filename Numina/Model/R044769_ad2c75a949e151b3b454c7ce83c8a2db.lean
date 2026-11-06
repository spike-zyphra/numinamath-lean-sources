import Mathlib

theorem algebra_2093 {y : ℝ → ℝ} {k : ℝ} (hy : y = fun x => 2 * x - 1) :
    (y x - 2 * x + 1) ∣ (4 * x * y x - 4 * x ^ 2 - (y x) ^ 2 - k) ↔ k = -1 := by
  have h1 : y x = 2 * x - 1 := by 
    rw [hy]
  -- Show that y x - 2 * x + 1 = 0
  have h2 : y x - 2 * x + 1 = 0 := by 
    rw [h1]
    ring
  -- Substitute y x in the expression
  have h3 : (4 * x * y x - 4 * x ^ 2 - (y x) ^ 2 - k) = -1 - k := by
    rw [h1]
    ring_nf
  -- Replace terms in the divisibility relation
  rw [h2, h3]
  -- Now the goal is (0 : ℝ) ∣ -1 - k ↔ k = -1
  -- The statement (0 : ℝ) ∣ (-1 - k) is equivalent to -1 - k = 0
  -- Prove the equivalence
  constructor
  · -- Forward: (0 : ℝ) ∣ -1 - k → k = -1
    intro h
    simp [dvd_zero] at h 
    linarith 
  · -- Backward: k = -1 → (0 : ℝ) ∣ -1 - k
    intro h 
    simp [dvd_zero]
    all_goals
      try { nlinarith }
      all_goals
        try { linarith }