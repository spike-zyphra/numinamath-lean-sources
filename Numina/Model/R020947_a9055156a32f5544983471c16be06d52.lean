import Mathlib

theorem algebra_21731 {x : ℕ} (hx : x ≠ 0) :
    (x : ℚ)⁻¹ > x ↔ False := by 
  constructor
  · -- Forward direction: if (x : ℚ)⁻¹ > x, then False.
    intro h
    have h1 : (x : ℚ) > 0 := by
      have h2 : x > 0 := by
        by_contra h3
        push_neg at h3
        have : x = 0 := by linarith
        contradiction
      have h3 : (x : ℚ) > (0 : ℚ) := by
        exact_mod_cast h2
      assumption
    have h2 : (x : ℚ) * (x : ℚ) ≥ (1 : ℚ) := by
      have hx3 : (x : ℚ) ≥ (1 : ℚ) := by
        have h4 : x ≥ 1 := by
          omega
        exact_mod_cast h4
      nlinarith
    -- We need to derive h3 : (x : ℚ) * (x : ℚ) < (1 : ℚ).
    -- which would contradict h2.
    -- Let's prove h3.
    have hx7 : (↑x : ℚ) < (1 / (↑x : ℚ) : ℚ) := by
      have hx8 : (x : ℚ)⁻¹ > (x : ℚ) := h
      have hx9 : (x : ℚ)⁻¹ = (1 / (↑x : ℚ) : ℚ) := by 
        field_simp
      linarith [hx9, hx8]
    have h4 : (x : ℚ) * (x : ℚ) < (1 : ℚ) := by
      have hx8 : (↑x : ℚ) > 0 := h1
      have hx9 : (↑x : ℚ) < (1 / (↑x : ℚ) : ℚ) := hx7
      have hx10 : (↑x : ℚ) * (↑x : ℚ) < (1 / (↑x : ℚ) : ℚ) * (↑x : ℚ) := by
        apply mul_lt_mul_of_pos_right hx9
        all_goals linarith
      have hx11 : (1 / (↑x : ℚ) : ℚ) * (↑x : ℚ) = (1 : ℚ) := by
        field_simp
        all_goals linarith
      linarith
    -- Contradicts h2 : (x : ℚ) * (x : ℚ) ≥ (1 : ℚ).
    -- goal is False
    linarith
    all_goals linarith
  · -- Backward direction: False implies anything.
    intro h
    cases h