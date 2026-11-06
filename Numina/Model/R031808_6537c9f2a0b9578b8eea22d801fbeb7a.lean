import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_320023 {a : ℝ} (ha : 0 < a ∧ a ≠ 1)
  (f : ℝ → ℝ) (hf : f = λ x => a ^ x + 3 * a)
  (g : ℝ → ℝ) (hg : ∀ x, ∃ y, g x = -y ∧ f y = x - a) :
  (∀ x, g x = -logb a (x - a) + 3 * a) ∧
  (∃ a : ℝ, 0 < a ∧ a ≠ 1 ∧ ∀ x ∈ Icc (a + 2) (a + 3), |f x - g (-x)| ≤ 1) ↔
  0 < a ∧ a ≤ (9 - sqrt 57) / 12 := by
  constructor
  · -- Forward direction: assuming the conjunction, proving the bound on a
    intro h
    rcases h with ⟨h1, h2⟩
    -- Use hypothesis for x = 0
    have h3 := hg 0
    rcases h3 with ⟨y, h31, h32⟩
    -- Now we have g 0 = -y ∧ f y = 0 - a = -a
    -- Expand definition of f
    rw [hf] at h32
    -- Now h32 becomes: a ^ y + 3 * a = -a
    have h4 : a ^ y + 3 * a = -a := by
      simpa using h32
    -- a^y must be positive
    have h5 : a ^ y > 0 := by
      apply Real.rpow_pos_of_pos ha.1
    -- Rearranging, we get a ^ y = -4 * a
    have h6 : a ^ y = -4 * a := by
      linarith
    -- But the right side is negative while left side is positive
    nlinarith [h5, ha.1, h6]
  · -- Backward direction: assuming the bound on a, proving the conjunction
    intro h
    -- Use hypothesis for x = 0
    have h3 := hg 0
    rcases h3 with ⟨y, h31, h32⟩
    -- Now we have g 0 = -y ∧ f y = 0 - a = -a
    -- Expand definition of f
    rw [hf] at h32
    -- Now h32 becomes: a ^ y + 3 * a = -a
    have h4 : a ^ y + 3 * a = -a := by
      simpa using h32
    -- a^y must be positive
    have h5 : a ^ y > 0 := by
      apply Real.rpow_pos_of_pos ha.1
    -- Rearranging, we get a ^ y = -4 * a
    have h6 : a ^ y = -4 * a := by
      linarith
    -- But the right side is negative while left side is positive
    nlinarith [h5, ha.1, h6]