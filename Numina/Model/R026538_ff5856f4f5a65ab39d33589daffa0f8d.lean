import Mathlib

theorem algebra_145346 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.logb a (3 * x ^ 2 - 2 * x)) :
    f 2 = 6 ↔ a = Real.sqrt 2 := by
  have h1 : f 2 = Real.logb a (3 * (2 : ℝ) ^ 2 - 2 * (2 : ℝ)) := hf 2
  have this : 3 * (2 : ℝ) ^ 2 - 2 * (2 : ℝ) = (8 : ℝ) := by
    norm_num
  have h2 : f 2 = Real.logb a (8 : ℝ) := by
    rw [h1, this]
  have h3 : Real.logb a (8 : ℝ) = 6 ↔ a = Real.sqrt 2 := by
    constructor
    · -- Real.logb a (8 : ℝ) = 6 → a = Real.sqrt 2
      intro h_eq
      have h4 : Real.logb a (8 : ℝ) = 6 := h_eq
      have h5 : Real.logb a (8 : ℝ) = (Real.log (8 : ℝ) ) / (Real.log (a : ℝ) ) := by 
        field_simp [Real.logb]
      rw [h5] at h4
      have h6 : Real.log ((8 : ℝ) ) = 6 * Real.log (a : ℝ) := by
        have h7 : (Real.log ((8 : ℝ) ) ) / (Real.log (a : ℝ) ) = 6 := by
          linarith
        have h10 : Real.log (a : ℝ) ≠ 0 := by
          by_contra h
          have : Real.log (a : ℝ) = 0 := by
            linarith
          have h11 : a = 1 := by
            rw [Real.log_eq_zero] at this
            rcases this with (r|m|r)
            · linarith
            · linarith
            · linarith
          have h12 : a ≠ 1 := ha.right
          contradiction
        field_simp at h7 ⊢
        all_goals linarith
      have h7 : Real.log ((8 : ℝ) ) = 3 * Real.log (2 : ℝ) := by
        calc
          Real.log ((8 : ℝ) ) = Real.log ((2 : ℝ) ^ 3 ) := by norm_num
          _ = 3 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      have h8 : 3 * Real.log (2 : ℝ) = 6 * Real.log (a : ℝ) := by
        rw [h7] at h6
        linarith
      have h9 : Real.log (2 : ℝ) = 2 * Real.log (a : ℝ) := by
        linarith
      have h10 : Real.log (a : ℝ) = (Real.log (2 : ℝ) ) / 2 := by
        linarith
      have h11 : Real.log (a : ℝ) = Real.log (Real.sqrt 2 : ℝ) := by
        have h12 : Real.log (Real.sqrt 2 : ℝ) = (Real.log (2 : ℝ) ) / 2 := by
          have h13 : Real.sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by 
            rw [Real.sqrt_eq_rpow]
          rw [h13]
          have h14 : Real.log ((2 : ℝ) ^ (1 / 2 : ℝ) ) = (1 / 2 : ℝ) * Real.log (2 : ℝ) := by
            rw [Real.log_rpow]
            all_goals linarith
          linarith [h14]
        linarith [h12, h10]
      have h12 : a = Real.sqrt 2 := by
        have h10' : Real.log a = Real.log (Real.sqrt 2 : ℝ) := h11
        have h13 : a = Real.sqrt 2 := by
          exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr (show 0 < Real.sqrt 2 by positivity)) h10'
        exact h13
      exact h12
    · -- Real.sqrt 2 = a → Real.logb a (8 : ℝ) = 6
      intro h_eq
      rw [h_eq]
      have h4 : Real.logb (Real.sqrt 2 : ℝ) (8 : ℝ) = 6 := by
        rw [Real.logb]
        have h5 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
          calc
            Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3 ) := by norm_num
            _ = 3 * Real.log (2 : ℝ) := by simp [Real.log_pow]
        have h6 : Real.log (Real.sqrt 2 : ℝ) = (1/2 : ℝ) * Real.log (2 : ℝ) := by
          have h7 : Real.sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by 
            rw [Real.sqrt_eq_rpow]
          rw [h7]
          have h8 : Real.log ((2 : ℝ) ^ (1 / 2 : ℝ) ) = (1 / 2 : ℝ) * Real.log (2 : ℝ) := by
            rw [Real.log_rpow]
            all_goals linarith
          linarith [h8]
        rw [h5, h6]
        have h9 : Real.log (2 : ℝ) > 0 := by
          apply Real.log_pos
          all_goals norm_num
        field_simp
        all_goals linarith
      exact h4
  rw [h2, h3]