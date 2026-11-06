import Mathlib

theorem algebra_308306 (f : ℝ → ℝ) (h₀ : ∀ x, f (x + 2) = f x)
    (h₁ : ∀ x, f (-x) = f x) (h₂ : ∀ x ∈ Set.Icc 2 3, f x = -x) :
    ∀ x ∈ Set.Icc (-2) 0, f x = -3 + abs (x + 1) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  by_cases h : x + 1 ≥ 0
  · -- Case where x + 1 >= 0 (i.e., x >= -1)
    have h3 : abs (x + 1) = x + 1 := by
      rw [abs_of_nonneg h]
    have h4 : x ≥ -1 := by
      linarith
    have h5 : -x ≥ 0 := by
      nlinarith
    have h6 : -x ≤ 1 := by
      nlinarith
    have h7 : f x = f (-x) := by
      have h8 : f (-x) = f x := h₁ x
      linarith
    have h8 : f (-x) = f ((-x) + 2) := by
      have h9 : f ((-x) + 2) = f (-x) := by
        specialize h₀ (-x)
        ring_nf at h₀ ⊢
        all_goals linarith
      linarith
    have h9 : (-x) + 2 ≥ 2 := by
      nlinarith
    have h10 : (-x) + 2 ≤ 3 := by
      nlinarith
    have h11 : (-x) + 2 ∈ Set.Icc 2 3 := by
      constructor <;> linarith
    have h12 : f ((-x) + 2) = - ((-x) + 2) := h₂ ((-x) + 2) h11
    rw [h3]
    rw [h7, h8, h12]
    all_goals ring
  · -- Case where x + 1 < 0 (i.e., x < -1)
    have h3 : abs (x + 1) = - (x + 1) := by
      rw [abs_of_neg (show x + 1 < 0 by linarith)]
    have h4 : x < -1 := by
      by_contra h'
      push_neg at h'
      have : x + 1 ≥ 0 := by linarith
      linarith
    -- For x ∈ [-2, -1], we have x + 4 ∈ [2, 3]
    have h5 : x + 4 ≥ 2 := by
      nlinarith
    have h6 : x + 4 ≤ 3 := by
      nlinarith
    have h7 : f x = f (x + 4) := by
      calc
        f x = f (x + 2) := by
          have h8 : f (x + 2) = f x := h₀ x
          linarith
        _ = f (x + 2 + 2) := by
          have h9 : f (x + 2 + 2) = f (x + 2) := by
            have : f (x + 2 + 2) = f (x + 2) := by
              specialize h₀ (x + 2)
              ring_nf at h₀ ⊢
              all_goals linarith
            linarith
          linarith
        _ = f (x + 4) := by
          ring_nf
    -- Now, x + 4 ∈ [2, 3], so use h₂
    have h8 : x + 4 ∈ Set.Icc 2 3 := by
      constructor <;> linarith
    have h9 : f (x + 4) = - (x + 4) := h₂ (x + 4) h8
    rw [h3]
    rw [h7, h9]
    all_goals ring