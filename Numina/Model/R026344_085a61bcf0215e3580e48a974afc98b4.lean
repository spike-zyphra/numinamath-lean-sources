import Mathlib

theorem algebra_20404 (x : ℝ) :
    abs (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 ↔
    x ∈ Set.Icc (-3) (-2) ∪ Set.Icc 0 1 := by 
  constructor 
  · -- Forward: abs (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 → x ∈ Set.Icc (-3) (-2) ∪ Set.Icc 0 1
    intro h
    have h1 : abs (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 := h
    have h2 : (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 ∨ (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≤ -1 := by 
      by_contra h
      push_neg at h
      have h3 : abs (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) < 1 := by 
        rw [abs_lt]
        constructor <;> linarith
      linarith 
    rcases h2 with h2 | h2
    · -- Case where 3 * (x + 1) / (x ^ 2 + 2 * x + 3) ≥ 1
      have h3 : 0 ≤ x := by 
        have h4 : (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 := h2
        apply (le_div_iff₀ (by 
          nlinarith [sq_nonneg (x + 1)]
        )).mp at h4
        nlinarith [sq_nonneg (x), sq_nonneg (x - 1)]
      have h4 : x ≤ 1 := by 
        have h5 : (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 := h2
        apply (le_div_iff₀ (by 
          nlinarith [sq_nonneg (x + 1)]
        )).mp at h5
        nlinarith [sq_nonneg (x), sq_nonneg (x - 1)]
      have h5 : x ∈ Set.Icc 0 1 := by
        constructor <;> linarith
      right 
      exact h5 
    · -- Case where 3 * (x + 1) / (x ^ 2 + 2 * x + 3) ≤ -1
      have h3 : -3 ≤ x := by 
        have h6 : (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≤ -1 := h2
        apply (div_le_iff₀ (by 
          nlinarith [sq_nonneg (x + 1)]
        )).mp at h6 
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x + 3), sq_nonneg (x + 1)]
      have h4 : x ≤ -2 := by 
        have h7 : (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≤ -1 := h2
        apply (div_le_iff₀ (by 
          nlinarith [sq_nonneg (x + 1)]
        )).mp at h7 
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x + 3), sq_nonneg (x + 1)]
      have h5 : x ∈ Set.Icc (-3) (-2) := by
        constructor <;> linarith
      left 
      exact h5 
  · -- Backward: x ∈ Set.Icc (-3) (-2) ∪ Set.Icc 0 1 → abs (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1
    intro h 
    rcases h with h | h 
    · -- Case where x ∈ [-3, -2]
      rw [Set.mem_Icc] at h 
      have h1 : -3 ≤ x := h.1
      have h2 : x ≤ -2 := h.2 
      have h3 : (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≤ -1 := by 
        have h4 : 0 < (x ^ 2 + 2 * x + 3) := by 
          nlinarith [sq_nonneg (x + 1)]
        apply (div_le_iff₀ h4).mpr 
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x + 3), sq_nonneg (x + 1)]
      have h4 : abs (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 := by
        cases' abs_cases (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) with h5 h5 <;> 
          linarith 
      linarith 
    · -- Case where x ∈ [0, 1]
      rw [Set.mem_Icc] at h 
      have h1 : 0 ≤ x := h.1
      have h2 : x ≤ 1 := h.2 
      have h3 : (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 := by 
        have h4 : 0 < (x ^ 2 + 2 * x + 3) := by 
          nlinarith [sq_nonneg (x + 1)]
        apply (le_div_iff₀ h4).mpr 
        nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
      have h4 : abs (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) ≥ 1 := by
        cases' abs_cases (3 * (x + 1) / (x ^ 2 + 2 * x + 3)) with h5 h5 <;> 
          linarith 
      linarith