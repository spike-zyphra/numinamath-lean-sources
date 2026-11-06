import Mathlib

theorem algebra_164699 {f : ℝ → ℝ} (hf : ∀ x, f (x + 2) = f x)
    (he : ∀ x, f (-x) = f x) (h : ∀ x ∈ Set.Icc 2 3, f x = x) :
    ∀ x ∈ Set.Icc (-2) 0, f x = 3 - abs (x + 1) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  by_cases h3 : x < -1
  · -- Case x < -1, so x ∈ [-2, -1)
    have h4 : x ≥ -2 := by linarith
    have h5 : x < -1 := by linarith
    have h6 : x + 2 ≥ 0 := by linarith
    have h7 : x + 2 < 1 := by linarith
    have h8 : x + 4 ∈ Set.Icc (2 : ℝ) (3 : ℝ) := by
      constructor
      · -- Show $2 \leq x + 4$
        nlinarith
      · -- Show $x + 4 \leq 3$
        nlinarith
    have h9 : f (x + 4) = x + 4 := by
      apply h
      exact h8
    have h10 : f x = f (x + 2) := by
      specialize hf x
      linarith
    have h11 : f (x + 2) = f (x + 4) := by
      specialize hf (x + 2)
      rw [show x + 2 + 2 = x + 4 by ring] at hf
      linarith
    have h12 : f x = x + 4 := by
      linarith [h9, h10, h11]
    have h13 : abs (x + 1) = - (x + 1) := by
      rw [abs_of_neg]
      linarith
    rw [h12]
    nlinarith [h13]
  · -- Case x ≥ -1, so x ∈ [-1, 0]
    have h4 : x ≥ -1 := by linarith
    have h5 : x ≤ 0 := by linarith
    have h6 : -x ≥ 0 := by linarith
    have h7 : -x ≤ 1 := by linarith
    have h8 : f (-x) = (-x) + 2 := by
      have h9 : (-x) + 2 ∈ Set.Icc (2 : ℝ) (3 : ℝ) := by
        constructor
        · -- Show $2 \leq (-x) + 2$
          nlinarith
        · -- Show $(-x) + 2 \leq 3$
          nlinarith
      have h9' : f ((-x) + 2) = (-x) + 2 := by
        apply h
        exact h9
      have h14 : f (-x) = f ((-x) + 2) := by
        specialize hf (-x)
        rw [show (-x) + 2 = (-x) + 2 by linarith] at hf
        linarith
      nlinarith [h14, h9']
    have h9 : f x = f (-x) := by
      specialize he x
      linarith
    have h10 : f x = (-x) + 2 := by
      linarith [h9, h8]
    have h13 : abs (x + 1) = x + 1 := by
      rw [abs_of_nonneg]
      nlinarith
    rw [h10]
    nlinarith [h13]