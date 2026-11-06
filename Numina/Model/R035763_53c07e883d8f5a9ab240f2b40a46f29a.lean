import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_263291 (m : ℝ) :
  IsLeast {m | ∃ a b : ℝ, ∀ x ∈ Icc (-1) 1, |x^2 + a * x + b| ≤ m * (x^2 + 1)} (1 / 3) := by
  constructor
  · -- Show that 1/3 is achievable.
    use 0, -1 / 3
    intro x hx
    have h1 : -1 ≤ x ∧ x ≤ 1 := by
      simpa using hx
    have h2 : x ^ 2 + (0) * x + (-1 / 3) = x ^ 2 - 1 / 3 := by ring
    rw [h2]
    have h3 : -1 ≤ x ∧ x ≤ 1 := by
      simpa using hx
    have h4 : -1 ≤ x := h3.1
    have h5 : x ≤ 1 := h3.2
    have h6 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have h7 : |x ^ 2 - 1 / 3| ≤ (1 / 3) * (x ^ 2 + 1) := by
      have h8 : - ((1 / 3) * (x ^ 2 + 1) ) ≤ x ^ 2 - 1 / 3 := by
        nlinarith
      have h9 : x ^ 2 - 1 / 3 ≤ (1 / 3) * (x ^ 2 + 1) := by
        nlinarith
      apply abs_le.mpr
      constructor
      · linarith
      · linarith
    simpa using h7
  · -- Show that 1/3 is the least such number
    intro m hm
    rcases hm with ⟨a, b, h⟩
    have h1 := h 1 (by norm_num)
    have h2 := h (-1) (by norm_num)
    have h3 := h (0) (by norm_num)
    have h4 := h (1 / 2) (by norm_num)
    have h5 := h (-1 / 2) (by norm_num)
    have h1' : |(1:ℝ)^2 + a * (1:ℝ) + b| ≤ m * ((1:ℝ)^2 + 1) := by simpa using h1
    have h2' : |(-1:ℝ)^2 + a * (-1:ℝ) + b| ≤ m * ((-1:ℝ)^2 + 1) := by simpa using h2
    have h3' : |(0:ℝ)^2 + a * (0:ℝ) + b| ≤ m * ((0:ℝ)^2 + 1) := by simpa using h3
    have h4' : |(1 / 2:ℝ)^2 + a * (1 / 2:ℝ) + b| ≤ m * ((1 / 2:ℝ)^2 + 1) := by simpa using h4
    have h5' : |(-1 / 2:ℝ)^2 + a * (-1 / 2:ℝ) + b| ≤ m * ((-1 / 2:ℝ)^2 + 1) := by simpa using h5
    have h11 : -2 * m ≤ 1 + a + b := by
      linarith [abs_le.mp h1']
    have h12 : 1 + a + b ≤ 2 * m := by
      linarith [abs_le.mp h1']
    have h21 : -2 * m ≤ 1 - a + b := by
      linarith [abs_le.mp h2']
    have h22 : 1 - a + b ≤ 2 * m := by
      linarith [abs_le.mp h2']
    have h31 : -m ≤ b := by
      linarith [abs_le.mp h3']
    have h32 : b ≤ m := by
      linarith [abs_le.mp h3']
    have h41 : - (5 / 4) * m ≤ (1 / 4) + a / 2 + b := by 
      linarith [abs_le.mp h4']
    have h42 : (1 / 4) + a / 2 + b ≤ (5 / 4) * m := by 
      linarith [abs_le.mp h4']
    have h51 : - (5 / 4) * m ≤ (1 / 4) - a / 2 + b := by
      linarith [abs_le.mp h5']
    have h52 : (1 / 4) - a / 2 + b ≤ (5 / 4) * m := by
      linarith [abs_le.mp h5']
    nlinarith