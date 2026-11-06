import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_280406 :
  IsLeast {x : ℝ | ∃ a b c d e f g : ℝ,
    a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ g ≥ 0 ∧
    a + b + c + d + e + f + g = 1 ∧
    x = max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g)} (1 / 3) := by
  constructor
  · -- Show 1/3 is in the set
    use 1 / 3, (0 : ℝ), (0 : ℝ), (1 / 3 : ℝ), (0 : ℝ), (0 : ℝ), (1 / 3 : ℝ)
    norm_num [max_assoc, max_comm, max_left_comm]
  · -- Show that 1/3 is the minimal element
    intro x hx
    rcases hx with ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg, hsum, hx⟩
    by_contra h
    push_neg at h
    have h1 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) < (1 / 3 : ℝ) := by
      linarith
    have h2 : a + b + c < (1 / 3 : ℝ) := by
      have h3 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ (a + b + c : ℝ) := by
        simp [max_le_iff]
      linarith [h1, h3]
    have h3 : b + c + d < (1 / 3 : ℝ) := by 
      have h4 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ (b + c + d : ℝ) := by
        simp [max_le_iff]
      linarith [h1, h4]
    have h4 : c + d + e < (1 / 3 : ℝ) := by
      have h5 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ (c + d + e : ℝ) := by
        simp [max_le_iff]
      linarith [h1, h5]
    have h5 : d + e + f < (1 / 3 : ℝ) := by
      have h6 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ (d + e + f : ℝ) := by
        simp [max_le_iff]
      linarith [h1, h6]
    have h6 : e + f + g < (1 / 3 : ℝ) := by
      have h7 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ (e + f + g : ℝ) := by
        simp [max_le_iff]
      linarith [h1, h7]
    linarith