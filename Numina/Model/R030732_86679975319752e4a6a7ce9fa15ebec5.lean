import Mathlib

theorem number_theory_66834 (n : ℕ) (hn : n > 0) :
    ¬∃ k : ℤ, (1 + Real.sqrt (8 * n + 1)) / 2 < k ∧ k < (1 + Real.sqrt (8 * n + 9)) / 2 := by 
  rintro ⟨k, h1, h2⟩
  have h1' : (1 + Real.sqrt (8 * (n : ℝ) + 1)) / 2 < (k : ℝ) := by exact_mod_cast h1
  have h2' : (k : ℝ) < (1 + Real.sqrt (8 * (n : ℝ) + 9)) / 2 := by exact_mod_cast h2
  have h3 : Real.sqrt (8 * (n : ℝ) + 1) < 2 * (k : ℝ) - 1 := by
    nlinarith
  have h4 : 2 * (k : ℝ) - 1 < Real.sqrt (8 * (n : ℝ) + 9) := by
    nlinarith
  by_cases h7 : (2 * (k : ℝ) - 1 : ℝ) ≥ 0
  · -- Assume $2 \cdot k - 1 \ge 0$.
    have h5 : (8 * (n : ℝ) + 1 : ℝ) < (2 * (k : ℝ) - 1) ^ 2 := by
      have h5 : Real.sqrt (8 * (n : ℝ) + 1 : ℝ) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (8 * (n : ℝ) + 1), Real.sq_sqrt (show (8 * (n : ℝ) + 1) ≥ 0 by positivity), h7]
    have h6 : (2 * (k : ℝ) - 1 : ℝ) ^ 2 < (8 * (n : ℝ) + 9 : ℝ) := by
      have h8 : (2 * (k : ℝ) - 1 : ℝ) ≥ 0 := h7
      have h9 : Real.sqrt (8 * (n : ℝ) + 9 : ℝ) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (8 * (n : ℝ) + 9), Real.sq_sqrt (show (8 * (n : ℝ) + 9 : ℝ) ≥ 0 by positivity), h8]
    have h7' : (8 * (n : ℝ) + 1 : ℝ) < (2 * (k : ℝ) - 1) ^ 2 := h5
    have h8' : (2 * (k : ℝ) - 1) ^ 2 < (8 * (n : ℝ) + 9 : ℝ) := h6
    have h9 : (8 * (n : ℤ) + 1) < (2 * k - 1) ^ 2 := by
      exact_mod_cast h7'
    have h10 : (2 * k - 1) ^ 2 < (8 * (n : ℤ) + 9) := by
      exact_mod_cast h8'
    -- Now integer k must satisfy $8n + 1 < (2k-1)^2 < 8n + 9$.
    -- Let $m = 2k - 1$. $m$ must be odd.
    -- So $8n + 1 < m^2 < 8n + 9$. We need contradiction.
    -- Because `m` odd implies $m^2 \equiv 1 \mod 8$.
    -- But $m^2$ must be from residue $2,3,4,5,6,7,0$. Contradiction.
    have h11 : (2 * k - 1 : ℤ) ^ 2 % 8 = 1 := by
      have h77 : (2 * k - 1 : ℤ) % 8 = 1 ∨ (2 * k - 1 : ℤ) % 8 = 3 ∨ (2 * k - 1 : ℤ) % 8 = 5 ∨ (2 * k - 1 : ℤ) % 8 = 7 := by
        omega
      rcases h77 with (h | h | h | h)
      · -- l = 1
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      · -- l = 3
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      · -- l = 5
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      · -- l = 7
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    omega
  · -- Assume `2 \cdot k - 1 < 0`.
    have h77 : (2 * (k : ℝ) - 1 : ℝ) < 0 := by
      by_contra h
      push_neg at h
      have : (2 * (k : ℝ) - 1 : ℝ) ≥ 0 := by linarith
      contradiction
    -- Contradicts, because `sqrt (8n+1) >=0` and `2k-1 < 0 => sqrt ... < 0` is invalid.
    have h8 : Real.sqrt (8 * (n : ℝ) + 1) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (8 * (n : ℝ) + 1)]