import Mathlib

theorem algebra_118463 (x y : ℤ) (hx : 5 ≤ x) :
    Real.sqrt (x - 5) = 15 - y^2 ↔ (x = 230 ∧ y = 0) ∨ (x = 201 ∧ y = 1) ∨ (x = 126 ∧ y = 2) ∨ (x = 41 ∧ y = 3) ∨ (x = 201 ∧ y = -1) ∨ (x = 126 ∧ y = -2) ∨ (x = 41 ∧ y = -3) := by
  constructor
  · -- Assume $\sqrt{x-5} = 15 - y^2$ (equation holds), prove the disjunction of solutions.
    intro h_eq
    have h1 : (x : ℝ) ≥ (5 : ℝ) := by exact_mod_cast hx
    have h2 : Real.sqrt (x - 5) ≥ 0 := by positivity
    -- From the equation, $15 - y^2 \geq 0$ implies $y^2 \leq 15$.
    have h3 : (15 - (y : ℝ) ^ 2) ≥ (0 : ℝ) := by linarith [h_eq, h2]
    have h4 : (y : ℝ) ^ 2 ≤ (15 : ℝ) := by nlinarith
    have h5 : ((x - 5 : ℝ) : ℝ) = (15 - (y : ℝ) ^ 2) ^ 2 := by
      calc
        ((x - 5 : ℝ) : ℝ) = (Real.sqrt (x - 5)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (15 - (y : ℝ) ^ 2) ^ 2 := by
          rw [h_eq]
    have h6 : (x - 5 : ℤ) = (15 - y^2) ^ 2 := by
      exact_mod_cast h5
    have h7 : y ≥ -3 := by
      by_contra h
      push_neg at h
      have h8 : y ≤ -4 := by omega
      nlinarith [show (y : ℝ) ≤ (-4 : ℝ) from by exact_mod_cast h8, sq_nonneg (y : ℝ)]
    have h8 : y ≤ 3 := by
      by_contra h
      push_neg at h
      have h9 : y ≥ 4 := by omega
      nlinarith [show (y : ℝ) ≥ (4 : ℝ) from by exact_mod_cast h9, sq_nonneg (y : ℝ)]
    interval_cases y <;> norm_num at h6 <;> omega
  · -- Assume the disjunction of solutions holds, prove $\sqrt{x - 5} = 15 - y^2$.
    rintro (h | h | h | h | h | h | h)
    · -- Case x = 230 ∧ y = 0
      rcases h with ⟨hx, hy⟩
      rw [show (x : ℝ) = (230 : ℝ) by exact_mod_cast hx, show (y : ℝ) = (0 : ℝ) by exact_mod_cast hy]
      have h1 : Real.sqrt ((230 : ℝ) - 5) = 15 - (0 : ℝ) ^ 2 := by
        rw [show (230 : ℝ) - 5 = (225 : ℝ) by norm_num]
        have : Real.sqrt (225 : ℝ) = 15 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [this]
        all_goals norm_num
      linarith [h1]
    · -- Case x = 201 ∧ y = 1
      rcases h with ⟨hx, hy⟩
      rw [show (x : ℝ) = (201 : ℝ) by exact_mod_cast hx, show (y : ℝ) = (1 : ℝ) by exact_mod_cast hy]
      have h1 : Real.sqrt ((201 : ℝ) - 5) = 15 - (1 : ℝ) ^ 2 := by
        rw [show (201 : ℝ) - 5 = (196 : ℝ) by norm_num]
        have : Real.sqrt (196 : ℝ) = 14 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [this]
        all_goals norm_num
      linarith [h1]
    · -- Case x = 126 ∧ y = 2
      rcases h with ⟨hx, hy⟩
      rw [show (x : ℝ) = (126 : ℝ) by exact_mod_cast hx, show (y : ℝ) = (2 : ℝ) by exact_mod_cast hy]
      have h1 : Real.sqrt ((126 : ℝ) - 5) = 15 - (2 : ℝ) ^ 2 := by
        rw [show (126 : ℝ) - 5 = (121 : ℝ) by norm_num]
        have : Real.sqrt (121 : ℝ) = 11 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [this]
        all_goals norm_num
      linarith [h1]
    · -- Case x = 41 ∧ y = 3
      rcases h with ⟨hx, hy⟩
      rw [show (x : ℝ) = (41 : ℝ) by exact_mod_cast hx, show (y : ℝ) = (3 : ℝ) by exact_mod_cast hy]
      have h1 : Real.sqrt ((41 : ℝ) - 5) = 15 - (3 : ℝ) ^ 2 := by
        rw [show (41 : ℝ) - 5 = (36 : ℝ) by norm_num]
        have : Real.sqrt (36 : ℝ) = 6 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [this]
        all_goals norm_num
      linarith [h1]
    · -- Case x = 201 ∧ y = -1
      rcases h with ⟨hx, hy⟩
      rw [show (x : ℝ) = (201 : ℝ) by exact_mod_cast hx, show (y : ℝ) = (-1 : ℝ) by exact_mod_cast hy]
      have h1 : Real.sqrt ((201 : ℝ) - 5) = 15 - (-1 : ℝ) ^ 2 := by
        rw [show (201 : ℝ) - 5 = (196 : ℝ) by norm_num]
        have : Real.sqrt (196 : ℝ) = 14 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [this]
        all_goals norm_num
      linarith [h1]
    · -- Case x = 126 ∧ y = -2
      rcases h with ⟨hx, hy⟩
      rw [show (x : ℝ) = (126 : ℝ) by exact_mod_cast hx, show (y : ℝ) = (-2 : ℝ) by exact_mod_cast hy]
      have h1 : Real.sqrt ((126 : ℝ) - 5) = 15 - (-2 : ℝ) ^ 2 := by
        rw [show (126 : ℝ) - 5 = (121 : ℝ) by norm_num]
        have : Real.sqrt (121 : ℝ) = 11 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [this]
        all_goals norm_num
      linarith [h1]
    · -- Case x = 41 ∧ y = -3
      rcases h with ⟨hx, hy⟩
      rw [show (x : ℝ) = (41 : ℝ) by exact_mod_cast hx, show (y : ℝ) = (-3 : ℝ) by exact_mod_cast hy]
      have h1 : Real.sqrt ((41 : ℝ) - 5) = 15 - (-3 : ℝ) ^ 2 := by
        rw [show (41 : ℝ) - 5 = (36 : ℝ) by norm_num]
        have : Real.sqrt (36 : ℝ) = 6 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [this]
        all_goals norm_num
      linarith [h1]