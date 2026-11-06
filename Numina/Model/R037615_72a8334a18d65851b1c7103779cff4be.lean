import Mathlib

theorem number_theory_3909 :
    IsLeast {x : ℤ | ∃ a b, a * b = 2023 ∧ x = a + b} (-2024) := by 
  constructor 
  · -- Show -2024 is in the set
    use -1, -2023 
    all_goals norm_num 
  · -- Show -2024 is minimal
    intro x hx 
    rcases hx with ⟨a, b, hprod, hx⟩ 
    by_contra h
    push_neg at h
    have hsum : a + b ≤ -2025 := by 
      linarith 
    have h1 : a ≤ -1 := by
      by_contra h2
      push_neg at h2
      have : a ≥ 0 := by nlinarith
      have h4 : b > 0 := by nlinarith [hprod, this]
      nlinarith
    -- Show b <= -1 in the same logic
    have h2 : b ≤ -1 := by
      by_contra h3
      push_neg at h3
      have : b ≥ 0 := by nlinarith
      have h5 : a > 0 := by nlinarith [hprod, this]
      nlinarith
    -- Now both a and b is negative
    -- Now they must be bounded. Let's know.
    have h4 : a * b = 2023 := hprod 
    have h6 : a ≤ -1 := h1
    have h7 : b ≤ -1 := h2
    -- Now both integers are negative. Then their product is (a * b) = 2023 
    -- But sum is ≤ -2025 → impossible.
    have h8 : a ≥ -2023 := by
      have h9 : b ≤ -1 := h7
      nlinarith [show a * b = 2023 by linarith] 
    -- The same ordering may not be apart of original. Multiply: f * e * b ≤ -2025.
    have h10 : b ≥ -2023 := by
      have h11 : a ≤ -1 := h6
      nlinarith [show a * b = 2023 by linarith] 
    interval_cases a <;> omega