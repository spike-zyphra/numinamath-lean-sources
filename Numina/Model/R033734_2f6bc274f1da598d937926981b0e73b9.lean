import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_322908 {f : ℝ → ℝ} (hf : StrictMono f)
  (hA : f 0 = -1) (hB : f 3 = 1) :
  {x | ¬(abs (f (x + 1)) < 1)} = {x | x ≤ -1 ∨ x ≥ 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume $|f(x+1)| \geq 1$, prove $x \leq -1 \lor x \geq 2$
    intro h
    have h1 : abs (f (x + 1)) ≥ 1 := by
      by_contra h1
      push_neg at h1
      have h2 : abs (f (x + 1)) < 1 := by
        simpa using h1
      contradiction
    have h2 : f (x + 1) ≤ -1 ∨ f (x + 1) ≥ 1 := by
      by_contra h3
      push_neg at h3
      have h4 : abs (f (x + 1)) < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      linarith [h1, h4]
    cases h2 with
    | inl h3 =>
      have h4 : x + 1 ≤ (0 : ℝ) := by
        by_contra h5
        push_neg at h5
        have h6 : f (x + 1) > f (0 : ℝ) := by
          apply hf.lt_iff_lt.mpr
          linarith
        have h7 : f (0 : ℝ) = -1 := by
          simpa using hA
        linarith [h6, h7, h3]
      have h8 : x ≤ -1 := by
        linarith
      left
      exact h8
    | inr h3 =>
      have h4 : x + 1 ≥ (3 : ℝ) := by
        by_contra h5
        push_neg at h5
        have h6 : f (x + 1) < f (3 : ℝ) := by
          apply hf.lt_iff_lt.mpr
          linarith
        have h7 : f (3 : ℝ) = 1 := by
          simpa using hB
        linarith [h6, h7, h3]
      have h8 : x ≥ 2 := by
        linarith
      right
      exact h8
  · -- Assume $x \leq -1 \lor x \geq 2$, prove $|f(x+1)| \geq 1$
    intro h
    rcases h with (h | h)
    · -- Case x ≤ -1
      have h3 : x + 1 ≤ (0 : ℝ) := by
        linarith
      have h4 : f (x + 1) ≤ f (0 : ℝ) := by
        apply hf.monotone
        all_goals linarith
      have h5 : f (0 : ℝ) = -1 := by
        simpa using hA
      have h6 : f (x + 1) ≤ -1 := by
        linarith [h4, h5]
      have h1 : abs (f (x + 1)) ≥ 1 := by
        cases abs_cases (f (x + 1)) with
        | inl h8 =>
          linarith
        | inr h8 =>
          linarith [h6, h8]
      linarith
    · -- Case x ≥ 2
      have h3 : x + 1 ≥ (3 : ℝ) := by
        linarith
      have h4 : f (x + 1) ≥ f (3 : ℝ) := by
        apply hf.monotone
        all_goals linarith
      have h5 : f (3 : ℝ) = 1 := by
        simpa using hB
      have h6 : f (x + 1) ≥ 1 := by
        linarith [h4, h5]
      have h1 : abs (f (x + 1)) ≥ 1 := by
        cases abs_cases (f (x + 1)) with
        | inl h8 =>
          linarith [h8, h6]
        | inr h8 =>
          linarith [h6, h8]
      linarith