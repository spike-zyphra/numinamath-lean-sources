import Mathlib

theorem number_theory_90650 (n : ℤ) (hn : 3 ≤ n) :
    ∃ q : ℚ, Real.sqrt ((n ^ 2 - 5) / (n + 1)) = q ↔ n = 3 := by 
  by_cases h : n = 3
  · -- Assume n = 3. Then the sqrt is equal to 1, so take q=1
    use 1
    rw [h]
    norm_num
  · -- Assume n ≠ 3
    have hne : n > 3 := by 
      by_contra h
      push_neg at h
      omega
    have h1 : (n + 1 : ℚ) > (0 : ℚ) := by
      have h' : 3 ≤ n := hn
      have h'2 : n + 1 ≥ 4 := by omega
      have h2 : (n + 1 : ℚ) ≥ (4 : ℚ) := by exact_mod_cast h'2
      nlinarith
    have h3 : Real.sqrt ((n ^ 2 - 5) / (n + 1)) > (0 : ℝ) := by
      have h4 : (n ^ 2 - 5 : ℝ) / (n + 1 : ℝ) > 0 := by
        have h5 : (n + 1 : ℝ) > 0 := by
          exact_mod_cast show (n + 1 : ℚ) > (0 : ℚ) by linarith
        have h6 : (n ^ 2 - 5 : ℝ) > 0 := by
          have : n ≥ 3 := by omega
          have : n ^ 2 ≥ 9 := by nlinarith
          have : (n ^ 2 - 5 : ℝ) ≥ (4 : ℝ) := by
            exact_mod_cast (show n ^ 2 - 5 ≥ 4 from by nlinarith)
          nlinarith
        exact div_pos h6 h5
      apply Real.sqrt_pos.mpr
      exact h4
    use (0 : ℚ)
    constructor
    · -- Assume sqrt = 0, which contradicts sqrt > 0
      intro h
      nlinarith [Real.sqrt_nonneg ((n ^ 2 - 5) / (n + 1)), h3]
    · -- Assume n = 3 from right side satisfies (which it doesn't, so makes LHS which should satisfy integer real Smith). 
      intro h
      have h5 : n = 3 := by
        exact_mod_cast h
      exfalso
      omega