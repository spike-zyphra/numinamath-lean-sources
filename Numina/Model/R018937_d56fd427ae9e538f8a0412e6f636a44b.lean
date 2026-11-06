import Mathlib

theorem algebra_252623 (f : ℝ → ℝ) (hf : f = fun x => x^2 + 2 * x + 3)
    (m : ℝ) (hm : m ≤ 0) (hmax : IsGreatest (Set.image f (Set.Icc m 0)) 3)
    (hmin : IsLeast (Set.image f (Set.Icc m 0)) 2) :
    m ∈ Set.Icc (-2) (-1) := by
  have h1 : ∀ x, f x = x ^ 2 + 2 * x + 3 := by
    intro x
    rw [hf]

  have h3 : 2 ∈ Set.image f (Set.Icc m 0) := by 
    have h4 : 2 ∈ Set.image f (Set.Icc m 0) := hmin.left
    exact h4
  rcases h3 with ⟨x, hx, hfx⟩

  have hx1 : m ≤ x := by
    have h4 : x ∈ Set.Icc m 0 := by
      simpa using hx
    exact h4.1
  have hx2 : x ≤ 0 := by
    have h4 : x ∈ Set.Icc m 0 := by
      simpa using hx
    exact h4.2
  
  rw [h1] at hfx 
  have eq1 : x ^ 2 + 2 * x + 3 = 2 := by
    linarith
  have h8 : x = -1 := by
    nlinarith
  
  have h9 : m ≤ -1 := by
    nlinarith [h8, hx1]

  have h4 : f m ≤ 3 := by
    have h5 : f m ∈ Set.image f (Set.Icc m 0) := by
      use m
      constructor
      · -- Show m ∈ Set.Icc m 0
        exact ⟨by linarith, by linarith⟩
      · -- Show f m = f m
        rfl 
    have h6 : ∀ y, y ∈ Set.image f (Set.Icc m 0) → y ≤ 3 := by 
      apply hmax.2
    specialize h6 (f m) h5
    linarith
  
  have h6 : m ^ 2 + 2 * m + 3 ≤ 3 := by
    have h7 : f m ≤ 3 := h4
    rw [h1] at h7 
    nlinarith

  have h7 : m ^ 2 + 2 * m ≤ 0 := by nlinarith
  constructor
  · -- Show that -2 ≤ m 
    nlinarith [sq_nonneg (m + 2), sq_nonneg (m + 1)]
  · -- Show that m ≤ -1
    linarith