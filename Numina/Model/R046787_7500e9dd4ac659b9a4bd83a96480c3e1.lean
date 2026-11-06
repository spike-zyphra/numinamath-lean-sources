import Mathlib

theorem algebra_268472 (n : ℕ) (hn : n > 2) :
    ∃ p q : ℚ, (n : ℝ) ^ ((1 : ℝ) / 3) = p + q * 2 ^ ((1 : ℝ) / 3) ↔
    ∃ k : ℕ, n = k ^ 3 := by
  by_cases h : ∃ k : ℕ, n = k ^ 3
  · -- If n is a cube, then we can set p = k and q = 0
    rcases h with ⟨k, hk⟩
    use (k : ℚ), (0 : ℚ)
    constructor
    · -- Assume (n : ℝ) ^ (1 / 3) = k + 0 * (2 : ℝ) ^ (1 / 3), need existence of k : n = k^3
      intro h_eq
      exact ⟨k, by simpa using hk⟩
    · -- Assume existence of k : n = k^3 need equation
      intro h_eq
      rcases h_eq with ⟨m, hm⟩
      have h_eq2 : (n : ℝ) ^ ((1 : ℝ) / 3) = (k : ℝ) := by
        rw [show (n : ℝ) = (k ^ 3 : ℝ) by exact_mod_cast (show (n : ℕ) = k ^ 3 by linarith [hm, hk] : (n : ℕ) = k ^ 3)]
        have h1 : ((k ^ 3 : ℝ) ^ ((1 : ℝ) / 3)) = (k : ℝ) := by
          have h2 : (k ^ 3 : ℝ) = (k : ℝ) ^ 3 := by norm_num
          rw [h2]
          have h3 : ((k : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (k : ℝ) := by
            rw [show ((k : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (k : ℝ) by
              have h5 : ((k : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (k : ℝ) := by
                rw [show (k : ℝ) ^ 3 = (k : ℝ) ^ 3 by rfl]
                rw [← Real.rpow_natCast, ← Real.rpow_mul]
                norm_num
                all_goals linarith
              linarith [h5]
            ]
          linarith
        linarith
      simp [h_eq2]
      <;> try { nlinarith }
      <;> tauto
  · -- If n is not a cube, then the existence can't be trivial.
    use (0 : ℚ)
    use (0 : ℚ)
    simp at h ⊢
    <;> try { tauto }
    <;> try { nlinarith }
    all_goals try { tauto }