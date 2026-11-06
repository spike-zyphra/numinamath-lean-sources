import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_160032 :
  IsLeast {x | ∃ a b c d e f g : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ g ≥ 0 ∧
    a + b + c + d + e + f + g = 1 ∧ x = max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g)} (1 / 3) := by
  constructor
  · -- Show 1/3 is in the set.
    use 1 / 3, (0 : ℝ), (0 : ℝ), 1 / 3, (0 : ℝ), (0 : ℝ), 1 / 3
    norm_num
    <;> try { simp [max_eq_left_of_lt, max_eq_right, le_refl] }
  · -- Show 1/3 is the minimum.
    intro x h
    rcases h with ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg, h1, hx⟩
    by_contra h'
    push_neg at h'
    -- Prove max <1/3
    have h2 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) < (1 / 3 : ℝ) := by
      linarith
    -- Let each part be less than 1/3
    have h3 : a + b + c < (1 / 3 : ℝ) := by
      have h3 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ a + b + c := by
        simp [max_le_iff]
      nlinarith
    -- Let each part be less than 1/3
    have h4 : b + c + d < (1 / 3 : ℝ) := by
      have h4 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ b + c + d := by
        simp [max_le_iff]
      nlinarith
    -- Let each part be less than 1/3
    have h5 : c + d + e < (1 / 3 : ℝ) := by
      have h5 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ c + d + e := by
        simp [max_le_iff]
      nlinarith
    -- Let each part be less than 1/3
    have h6 : d + e + f < (1 / 3 : ℝ) := by
      have h6 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ d + e + f := by
        simp [max_le_iff]
      nlinarith
    -- Let each part be less than 1/3
    have h7 : e + f + g < (1 / 3 : ℝ) := by
      have h7 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ e + f + g := by
        simp [max_le_iff]
      nlinarith
    -- Sum up all inequalities and derive contradiction
    linarith