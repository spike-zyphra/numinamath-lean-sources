import Mathlib


theorem number_theory_623167 :
    IsLeast {x : ℕ | x > 0 ∧ ∃ z : ℕ, z > 0 ∧ z = √(x ^ 2 + 2025)} 24 := by
  constructor
  · -- Show that 24 is in the set
    constructor
    · norm_num
    · use 51
      constructor
      · norm_num
      · -- Show that 51 = sqrt(24^2 + 2025)
        have h1 : (24 ^ 2 + 2025 : ℝ) = (51 : ℝ) ^ 2 := by norm_num
        have h2 : Real.sqrt ((24 ^ 2 + 2025 : ℝ)) = (51 : ℝ) := by
          rw [show (24 ^ 2 + 2025 : ℝ) = (51 : ℝ) ^ 2 by linarith]
          rw [Real.sqrt_sq (by norm_num)]
        norm_num at h2 ⊢
        all_goals linarith
  · -- Show 24 is the minimal element
    intro x hx
    rcases hx with ⟨hx_pos, z, hz_pos, h_eq⟩
    by_contra h
    push_neg at h
    -- Now we have x ≤ 23
    -- Now we need to show this leads to a contradiction
    have h30 : (z : ℝ) ^ 2 = (x ^ 2 + 2025 : ℝ) := by
      have h1 : (z : ℝ) = Real.sqrt ((x ^ 2 + 2025 : ℝ)) := by
        exact_mod_cast h_eq
      have h2 : (z : ℝ) ≥ 0 := by
        have h3 : (z : ℝ) = Real.sqrt ((x ^ 2 + 2025 : ℝ)) := h1
        have h14 : Real.sqrt ((x ^ 2 + 2025 : ℝ)) ≥ 0 := Real.sqrt_nonneg ((x ^ 2 + 2025 : ℝ))
        linarith [h3, h14]
      have h3 : (z : ℝ) ^ 2 = (x ^ 2 + 2025 : ℝ) := by
        calc
          (z : ℝ) ^ 2 = (Real.sqrt ((x ^ 2 + 2025 : ℝ)) ) ^ 2 := by rw [h1]
          _ = (x ^ 2 + 2025 : ℝ) := by rw [Real.sq_sqrt]; positivity
      linarith [h3]
    have h4 : z ^ 2 = x ^ 2 + 2025 := by
      have h8 : (z : ℝ) ^ 2 = (x ^ 2 + 2025 : ℝ) := h30
      exact_mod_cast h8
    have h5 : x < 24 := by linarith
    have h8 : z ^ 2 < (52 : ℕ) ^ 2 := by
      have h10 : x ≤ 23 := by omega
      have h100 : x ^ 2 ≤ (23 : ℕ) ^ 2 := by nlinarith [h10]
      nlinarith [h4, h100]
    have h19 : z < (52 : ℕ) := by
      nlinarith
    have h80 : z ≤ 51 := by omega
    interval_cases x <;> try { 
      omega 
    } <;> try { 
      interval_cases z <;> omega 
    }