import Mathlib

theorem algebra_286357 {f : ℝ → ℝ} (hf : ∀ x, f (x + 2) = f x)
    (h : ∀ x ∈ Set.Icc (-1) 1, f x = x ^ 2 + 1) :
    ∀ x ∈ Set.Icc (-3) 3, f x = if x ∈ Set.Icc (-3) (-1) then x ^ 2 + 4 * x + 5 else f (x - 2) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  by_cases h2 : x ≤ -1
  · -- x ≤ -1, so x ∈ [-3, -1]
    have h3 : x ≥ -3 := by linarith
    have h4 : x ≤ -1 := h2
    have hx5 : x + 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · -- Show that -1 ≤ x + 2
        linarith
      · -- Show that x + 2 ≤ 1
        nlinarith
    have h5 : f (x + 2) = (x + 2) ^ 2 + 1 := h (x + 2) hx5
    have h5' : f x = (x + 2) ^ 2 + 1 := by 
      have h6 : f (x + 2) = f x := by
        specialize hf x
        linarith
      linarith [h6, h5]
    have h11 : x ∈ Set.Icc (-3 : ℝ) (-1) := by
      constructor
      · -- Show that -3 ≤ x
        linarith
      · -- Show that x ≤ -1
        linarith
    simp [h11, h5']
    all_goals nlinarith
  · -- x > -1, so x ∈ (-1, 3]
    have h4 : x > -1 := by linarith
    by_cases h5 : x ≤ 1
    · -- x ≤ 1, so x ∈ (-1, 1]
      have hx_in : x ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor
        · -- Show that -1 ≤ x
          nlinarith
        · -- Show that x ≤ 1
          linarith
      have h6 : f x = x ^ 2 + 1 := h x hx_in
      have h7 : ¬ (x ∈ Set.Icc (-3 : ℝ) (-1)) := by 
        intro h8
        have h81 : x ≤ -1 := by 
          have h9 : x ∈ Set.Icc (-3 : ℝ) (-1) := h8
          exact h9.2
        linarith
      have h8 : f x = f (x - 2) := by 
        have hf' : f (x - 2 + 2) = f (x - 2) := hf (x - 2)
        have h9 : x - 2 + 2 = x := by ring
        rw [h9] at hf'
        linarith
      simp [h7, h8, h6]
      all_goals nlinarith
    · -- x > 1, so x ∈ (1, 3]
      have h6 : x > 1 := by nlinarith
      have h7 : ¬ (x ∈ Set.Icc (-3 : ℝ) (-1)) := by 
        intro h11
        have h9 : x ≤ -1 := by 
          have h10 : x ∈ Set.Icc (-3 : ℝ) (-1) := h11
          exact h10.2
        linarith
      have h8 : f x = f (x - 2) := by 
        -- We need to show f x = f (x - 2)
        have hf' : f (x - 2 + 2) = f (x - 2) := hf (x - 2)
        have h9 : x - 2 + 2 = x := by ring
        rw [h9] at hf'
        linarith
      simp [h7, h8]
      all_goals nlinarith