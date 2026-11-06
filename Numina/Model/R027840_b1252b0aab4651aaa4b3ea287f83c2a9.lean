import Mathlib

open Real Set
open scoped Real

theorem algebra_135647 {x y : ℝ} (h : sin x + cos y = 1 + sin (x - y) * cos (x + y)) :
    cos (x + y) = 1 ↔ ∃ k : ℤ, x + y = 2 * π * k := by
  constructor
  · -- Assume cos (x + y) = 1, prove ∃ k : ℤ, x + y = 2 * π * k
    intro hcos
    have h1 : cos (x + y) = 1 := hcos
    have h2 : ∃ k : ℤ, x + y = 2 * π * k := by
      have h3 : cos (x + y) = 1 := h1
      rw [Real.cos_eq_one_iff] at h3
      rcases h3 with ⟨k, hk⟩
      refine ⟨k, by linarith⟩
    exact h2
  · -- Assume ∃ k : ℤ, x + y = 2 * π * k, prove cos (x + y) = 1
    rintro ⟨k, hk⟩
    have h1 : x + y = 2 * π * (k : ℝ) := by
      linarith [hk]
    have h2 : cos (x + y) = 1 := by
      have h3 : x + y = 2 * π * (k : ℝ) := h1
      have h4 : cos (x + y) = cos (2 * π * (k : ℝ)) := by
        rw [h3]
      have h5 : cos (2 * π * (k : ℝ)) = 1 := by
        have h6 : 2 * π * (k : ℝ) = (k : ℝ) * (2 * π) := by ring
        rw [h6]
        have h7 : cos ((k : ℝ) * (2 * π)) = 1 := by
          have h8 : cos ((k : ℝ) * (2 * π)) = 1 := by
            have : (k : ℝ) * (2 * π) = (k : ℤ) * (2 * π) := by simp
            rw [this]
            exact Real.cos_int_mul_two_pi ↑k
          linarith
        linarith
      linarith
    exact h2