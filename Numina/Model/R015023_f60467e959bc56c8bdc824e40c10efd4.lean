import Mathlib

theorem algebra_220442 (a : ℝ) :
    (∃! n : ℕ, n^2 - (a + 2) * n + 2 - a < 0) ↔
    1 / 2 < a ∧ a ≤ 2 / 3 := by
  constructor
  · -- Assume that there exists a unique natural number n such that the inequality holds
    intro h
    rcases h with ⟨n, ⟨hn, h1⟩⟩
    by_cases h3 : n = 0 
    · -- n = 0 
      rw [h3] at hn 
      norm_num at hn
      -- This implies a > 2, which contradicts uniqueness
      -- Let's show contradiction 
      have h4 : (2 : ℝ) < a := by nlinarith
      have h5 := h1 1 (by 
        norm_num 
        nlinarith 
      )
      simp [h3] at h5 
    by_cases h3 : n = 1 
    · -- n = 1 
      rw [h3] at hn 
      have h5 : a > (1 / 2 : ℝ) := by 
        norm_num at hn 
        nlinarith 
      have h6 : a ≤ (2 / 3 : ℝ) := by
        by_contra h7 
        push_neg at h7 
        have h8 := h1 2 (by 
          norm_num 
          nlinarith 
        )
        simp [h3] at h8 
        all_goals 
          omega 
      exact ⟨h5, h6⟩
    · -- n ≥ 2 
      have h4 : n ≥ 2 := by 
        omega 
      -- Let's show contradiction
      have h4' : (n : ℝ) ≥ (2 : ℝ) := by 
        exact_mod_cast h4 
      -- Now prove that it's impossible
      have h7 := h1 1 (by 
        norm_num 
        nlinarith 
      )
      have h8 : (1 : ℕ) = n := h7 
      omega 
  · -- Now, prove the reverse.
    intro h 
    rcases h with ⟨ha1, ha2⟩ 
    use 1 
    constructor 
    · -- Show that 1 is indeed a solution.
      norm_num 
      nlinarith 
    · -- Show that 1 is the unique solution.
      intro m hm
      have hm1 : (m : ℝ) ^ 2 - (a + 2) * (m : ℝ) + 2 - a < (0 : ℝ) := by 
        simpa using hm 
      by_cases h3 : m < 2 
      · -- Assume m < 2, then m = 0 or 1 
        have : m = 0 ∨ m = 1 := by 
          omega 
        rcases this with (r | r) 
        · -- If m = 0 
          rw [r] at hm1 
          norm_num at hm1 
          all_goals 
            nlinarith 
        · -- If m = 1 
          omega 
      · -- Assume m ≥ 2 
        have h3 : m ≥ 2 := by 
          omega 
        have h4 : (m : ℝ) ≥ (2 : ℝ) := by 
          exact_mod_cast h3 
        have h5 : (m : ℝ) ^ 2 - (a + 2) * (m : ℝ) + 2 - a ≥ 0 := by 
          nlinarith [sq_nonneg ((a + 2) : ℝ), sq_nonneg (( (m : ℝ) - 2 ) : ℝ), sq_nonneg ((a - (2 / 3) : ℝ)), sq_nonneg ((m : ℝ) - (2 : ℝ)), sq_nonneg ((a - 2 : ℝ))]
        linarith