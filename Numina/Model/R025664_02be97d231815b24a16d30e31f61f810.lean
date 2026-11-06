import Mathlib

open Set Real

theorem algebra_266632 (a : ℝ) (ha : -2 ≤ a) (B C : Set ℝ)
    (hB : B = {x | ∃ t ∈ Icc (-2) a, x = 2 * t + 3}) (hC : C = {x | ∃ t ∈ Icc (-2) a, x = t ^ 2})
    (h : C ⊆ B) :
    1 / 2 ≤ a ∧ a ≤ 3 := by

  -- Show that 4 ∈ C
  have h1 : 4 ∈ C := by
    rw [hC]
    use -2
    constructor
    · -- Show that -2 ∈ Icc (-2) a
      exact ⟨by linarith, by linarith⟩
    · -- Show that 4 = (-2) ^ 2
      norm_num
  -- Since C ⊆ B, we have 4 ∈ B
  have h2 : 4 ∈ B := h h1
  -- Unfold the definition of B
  rw [hB] at h2
  rcases h2 with ⟨t, ht, ht1t⟩
  rcases ht with ⟨ht1, ht2⟩
  -- From 4 = 2 * t + 3, we can solve for t
  have ht3 : t = 1 / 2 := by linarith
  -- Substitute t = 1/2 into the interval condition -2 ≤ t ≤ a
  rw [ht3] at ht1 ht2
  have ha1 : 1 / 2 ≤ a := by linarith
  -- Now pick the element a² ∈ C
  have h4 : a ^ 2 ∈ C := by
    rw [hC]
    use a
    constructor
    · -- Show that a ∈ Icc (-2) a
      exact ⟨by linarith, by linarith⟩
    all_goals
      -- Show that a^2 = a^2
      all_goals
        linarith
  -- Since C ⊆ B, we have a² ∈ B
  have h5 : a ^ 2 ∈ B := h h4
  -- Unfold the definition of B
  rw [hB] at h5
  rcases h5 with ⟨t, ht, ht_eq⟩
  rcases ht with ⟨ht1, ht2⟩
  -- Now in the element a^2 = 2 * t + 3, solve for t
  -- And apply interval condition
  have ha2 : a ≤ 3 := by
    nlinarith
  -- Now we can conclude 1/2 ≤ a and a ≤ 3
  exact ⟨ha1, ha2⟩