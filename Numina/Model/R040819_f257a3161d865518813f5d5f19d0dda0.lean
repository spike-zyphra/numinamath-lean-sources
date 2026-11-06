import Mathlib

open Set

lemma lemma_1 (x : ℝ) (hx : x ≠ -1/3) : (9 * x^2 - 1) / (x + 1/3) = 9 * x - 3 := by
  have h1 : x + 1/3 ≠ 0 := by
    by_contra h
    have h2 : x = -1/3 := by
      linarith
    contradiction
  have h2 : 9 * x^2 - 1 = (3 * x - 1) * (3 * x + 1) := by
    ring
  have h3 : x + 1/3 = (1/3) * (3 * x + 1) := by
    field_simp
    <;> ring
  have h4 : 3 * x + 1 ≠ 0 := by
    by_contra h
    have h5 : x = -1/3 := by
      linarith
    contradiction
  rw [h2, h3]
  field_simp [h4]
  <;> ring_nf

theorem calculus_156783 (ε : ℝ) (hε : ε > 0) :
    ∃ δ, δ > 0 ∧ ∀ x, (x ∈ Set.Ioo (-1/3 - δ) (-1/3) ∨ x ∈ Set.Ioo (-1/3) (-1/3 + δ)) →
    abs ((9 * x^2 - 1)/(x + 1/3) + 6) < ε := by
  use ε / 9
  constructor
  · -- Show $\delta > 0$
    linarith
  · -- Show the implication holds
    intro x h
    rcases h with (h | h)
    · -- Case where x ∈ (-1/3 - δ, -1/3)
      rcases h with ⟨h1, h2⟩
      have hx1 : x < -1/3 := by linarith
      have hx2 : -1/3 - ε / 9 < x := by linarith
      have h_eq : (9 * x^2 - 1) / (x + 1/3) = 9 * x - 3 := by
        apply lemma_1
        linarith
      rw [h_eq]
      have h3 : abs ((9 * x - 3 + 6) : ℝ) = abs ((9 * (x + 1/3) ) : ℝ) := by
        have h_eq1 : (9 * x - 3 + 6 : ℝ) = 9 * (x + 1/3) := by
          ring
        rw [h_eq1]
      rw [h3]
      have h4 : abs ((9 * (x + 1/3) : ℝ)) = 9 * abs ((x + 1/3 : ℝ)) := by
        calc
          abs ((9 * (x + 1/3) : ℝ))
              = abs (9 : ℝ) * abs ((x + 1/3 : ℝ)) := by rw [abs_mul]
          _ = (9 : ℝ) * abs ((x + 1/3 : ℝ)) := by
            norm_num
      rw [h4]
      have h5 : abs ((x + 1/3 : ℝ)) < ε / 9 := by
        have h6 : (x + 1/3 : ℝ) < 0 := by
          nlinarith
        have h7 : abs ((x + 1/3 : ℝ)) = - (x + 1/3) := by
          rw [abs_of_neg h6]
        rw [h7]
        nlinarith
      nlinarith
    · -- Case where x ∈ (-1/3, -1/3 + δ)
      rcases h with ⟨h1, h2⟩
      have hx1 : -1/3 < x := by linarith
      have hx2 : x < -1/3 + ε / 9 := by linarith
      have h_eq : (9 * x^2 - 1) / (x + 1/3) = 9 * x - 3 := by
        apply lemma_1
        linarith
      rw [h_eq]
      have h3 : abs ((9 * x - 3 + 6) : ℝ) = abs ((9 * (x + 1/3) ) : ℝ) := by
        have h_eq1 : (9 * x - 3 + 6 : ℝ) = 9 * (x + 1/3) := by
          ring
        rw [h_eq1]
      rw [h3]
      have h4 : abs ((9 * (x + 1/3) : ℝ)) = 9 * abs ((x + 1/3 : ℝ)) := by
        calc
          abs ((9 * (x + 1/3) : ℝ))
              = abs (9 : ℝ) * abs ((x + 1/3 : ℝ)) := by rw [abs_mul]
          _ = (9 : ℝ) * abs ((x + 1/3 : ℝ)) := by
            norm_num
      rw [h4]
      have h5 : abs ((x + 1/3 : ℝ)) < ε / 9 := by
        have h6 : (x + 1/3 : ℝ) > 0 := by
          nlinarith
        have h7 : abs ((x + 1/3 : ℝ)) = (x + 1/3) := by
          rw [abs_of_pos h6]
        rw [h7]
        nlinarith
      nlinarith