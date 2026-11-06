import Mathlib

open Real

theorem inequalities_81003 (A B : ℝ) (hA : A > 0) (hB : B > 0)
    (hA' : round A = 20) (hB' : round B = 23) :
    ⌊(100 * A / B)⌋ ≤ 91 := by
  have h1 : A ≥ 19.5 := by
    have h1 : round A = 20 := hA'
    have h2 : ⌊A + (1 / 2 : ℝ)⌋ = 20 := by
      rw [round_eq] at h1
      exact_mod_cast h1
    have h3 : (A + (1 / 2 : ℝ)) ≥ (20 : ℝ) := by
      have h4 : ⌊A + (1 / 2 : ℝ)⌋ = 20 := h2
      have h5 : (⌊A + (1 / 2 : ℝ)⌋ : ℝ) ≤ (A + (1 / 2 : ℝ)) := by exact Int.floor_le (A + (1 / 2 : ℝ))
      have h6 : (⌊A + (1 / 2 : ℝ)⌋ : ℝ) = (20 : ℝ) := by exact_mod_cast h4
      linarith
    linarith
  have h2 : A < 20.5 := by
    have h1 : round A = 20 := hA'
    have h2 : ⌊A + (1 / 2 : ℝ)⌋ = 20 := by 
      rw [round_eq] at h1
      exact_mod_cast h1
    have h3 : (A + (1 / 2 : ℝ)) < (21 : ℝ) := by
      have h4 : ⌊A + (1 / 2 : ℝ)⌋ = 20 := h2
      have h5 : (A + (1 / 2 : ℝ)) < (⌊A + (1 / 2 : ℝ)⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (A + (1 / 2 : ℝ))
      have h6 : (⌊A + (1 / 2 : ℝ)⌋ : ℝ) = (20 : ℝ) := by exact_mod_cast h4
      linarith
    linarith
  have h3 : B ≥ 22.5 := by
    have h1 : round B = 23 := hB'
    have h2 : ⌊B + (1 / 2 : ℝ)⌋ = 23 := by 
      rw [round_eq] at h1
      exact_mod_cast h1
    have h3 : (B + (1 / 2 : ℝ)) ≥ (23 : ℝ) := by
      have h4 : ⌊B + (1 / 2 : ℝ)⌋ = 23 := h2
      have h5 : (⌊B + (1 / 2 : ℝ)⌋ : ℝ) ≤ (B + (1 / 2 : ℝ)) := by exact Int.floor_le (B + (1 / 2 : ℝ))
      have h6 : (⌊B + (1 / 2 : ℝ)⌋ : ℝ) = (23 : ℝ) := by exact_mod_cast h4
      linarith
    linarith
  have h4 : B < 23.5 := by
    have h1 : round B = 23 := hB'
    have h2 : ⌊B + (1 / 2 : ℝ)⌋ = 23 := by 
      rw [round_eq] at h1
      exact_mod_cast h1
    have h3 : (B + (1 / 2 : ℝ)) < (24 : ℝ) := by
      have h4 : ⌊B + (1 / 2 : ℝ)⌋ = 23 := h2
      have h5 : (B + (1 / 2 : ℝ)) < (⌊B + (1 / 2 : ℝ)⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (B + (1 / 2 : ℝ))
      have h6 : (⌊B + (1 / 2 : ℝ)⌋ : ℝ) = (23 : ℝ) := by exact_mod_cast h4
      linarith
    linarith
  have h5 : 100 * A < 92 * B := by 
    nlinarith
  have h6 : (100 * A / B) < (92 : ℝ) := by 
    have h7 : 0 < B := hB
    have h8 : 100 * A < 92 * B := h5
    have h9 : (100 * A / B) < (92 : ℝ) := by 
      apply (div_lt_iff₀ (by linarith)).mpr
      linarith
    linarith
  have h7 : ⌊(100 * A / B)⌋ ≤ 91 := by
    by_contra h
    push_neg at h
    have h10 : ⌊(100 * A / B)⌋ ≥ 92 := by linarith
    have h11 : (100 * A / B) ≥ (92 : ℝ) := by
      have h12 : ⌊(100 * A / B)⌋ ≥ 92 := h10
      have h13 : (⌊(100 * A / B)⌋ : ℝ) ≥ (92 : ℝ) := by 
        exact_mod_cast h12
      have h14 : (100 * A / B) ≥ (⌊(100 * A / B)⌋ : ℝ) := by 
        exact_mod_cast (Int.floor_le (100 * A / B))
      linarith [h13, h14]
    linarith [h11, h6]
  exact h7