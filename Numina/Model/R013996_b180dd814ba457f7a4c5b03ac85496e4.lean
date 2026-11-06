import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189886 (x : ℝ) (hx : x ≠ 5) :
    (3 * x ^ 2 - 10 * x + 3) / (x ^ 2 - 10 * x + 25) > 0 ↔
    x ∈ Iio (1 / 3) ∪ Ioo 3 5 ∪ Ioi 5 := by
  have h1 : x ^ 2 - 10 * x + 25 > 0 := by
    have h2 : x ^ 2 - 10 * x + 25 = (x - 5) ^ 2 := by
      nlinarith
    rw [h2]
    have h3 : (x - 5) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      intro h4
      apply hx
      linarith
    linarith
  have h2 : (3 * x ^ 2 - 10 * x + 3) / (x ^ 2 - 10 * x + 25) > 0 ↔ 3 * x ^ 2 - 10 * x + 3 > 0 := by
    have pos1 : x ^ 2 - 10 * x + 25 > 0 := h1
    apply Iff.intro
    · -- Forward
      intro h
      apply div_pos_iff.mp at h
      cases h with
      | inl h4 =>
        linarith
      | inr h5 =>
        nlinarith
    · -- Backward
      intro h
      apply div_pos
      all_goals linarith
  rw [h2]
  constructor
  · -- Proof of (3 * x ^ 2 - 10 * x + 3 > 0) → (x ∈ Iio (1 / 3) ∪ Ioo 3 5 ∪ Ioi 5)
    intro h
    have h3 : (3 * x - 1) * (x - 3) > 0 := by
      nlinarith
    have h4 : x < (1 / 3 : ℝ) ∨ x > (3 : ℝ) := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (x - 3), sq_nonneg (x - 5)]
    rcases h4 with (h4 | h4)
    · -- Case x < 1/3
      have h5 : x ∈ Iio (1 / 3) ∪ Ioo 3 5 ∪ Ioi 5 := by
        simp at *
        all_goals 
          try { tauto }
          try { nlinarith }
          try { tauto }
      exact h5
    · -- Case x > 3
      by_cases h7 : x < (5 : ℝ)
      · -- Case x < 5
        have h5 : x ∈ Iio (1 / 3) ∪ Ioo 3 5 ∪ Ioi 5 := by
          have h8 : x ∈ Ioo (3 : ℝ) (5 : ℝ) := ⟨by linarith, by linarith⟩
          simp at *
          all_goals 
            try { tauto }
            try { nlinarith }
        exact h5
      · -- Case x ≥ 5
        have h8 : x ≥ (5 : ℝ) := by linarith
        have h5 : x ∈ Iio (1 / 3) ∪ Ioo 3 5 ∪ Ioi 5 := by
          have h82 : x > (5 : ℝ) := by 
            by_contra h
            push_neg at h
            have h9 : x = (5 : ℝ) := by linarith
            contradiction
          have h9 : x ∈ Ioi (5 : ℝ) := by
            simpa using h82
          simp at *
          all_goals 
            try { tauto }
            try { nlinarith }
        exact h5
  · -- Proof of (x ∈ Iio (1 / 3) ∪ Ioo 3 5 ∪ Ioi 5) → (3 * x ^ 2 - 10 * x + 3 > 0)
    intro h
    rcases h with (hA | hB)
    · -- Case x ∈ Iio (1/3) ∪ Ioo 3 5
      rcases hA with (hA' | hB')
      · -- Case x ∈ Iio (1/3)
        have h1 : x < (1 / 3 : ℝ) := by
          simpa using hA'
        have h3 : (3 * x - 1) * (x - 3) > 0 := by
          nlinarith
        nlinarith
      · -- Case x ∈ Ioo 3 5
        rcases hB' with ⟨h4, h5⟩
        have h3 : (3 * x - 1) * (x - 3) > 0 := by
          nlinarith
        nlinarith
    · -- Case x ∈ Ioi 5
      have h3 : x > (5 : ℝ) := by
        simpa using hB
      have h4 : (3 * x - 1) * (x - 3) > 0 := by
        nlinarith
      nlinarith