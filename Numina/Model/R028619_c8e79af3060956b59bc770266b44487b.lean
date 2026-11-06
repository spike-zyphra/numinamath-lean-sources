import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_110665 {f : ℝ → ℝ}
  (hf : StrictMono f)
  (hA : f 0 = -2)
  (hB : f 3 = 2) :
  {x | abs (f (x + 1)) ≥ 2} = {x | x ≤ -1 ∨ x ≥ 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume $|f(x + 1)| \geq 2$, we need to show $x \leq -1$ or $x \geq 2$.
    intro h
    have h1 : abs (f (x + 1)) ≥ 2 := h
    have h2 : f (x + 1) ≤ -2 ∨ f (x + 1) ≥ 2 := by
      by_cases h3 : f (x + 1) ≥ 0
      · -- If f(x+1) ≥ 0, then |f(x+1)| = f(x+1)
        have h4 : abs (f (x + 1)) = f (x + 1) := abs_of_nonneg h3
        rw [h4] at h1
        right
        linarith
      · -- If f(x+1) < 0, then |f(x+1)| = -f(x+1)
        have h4 : abs (f (x + 1)) = -f (x + 1) := abs_of_neg (lt_of_not_ge h3)
        rw [h4] at h1
        left
        linarith
    rcases h2 with (h2 | h2)
    · -- Assume f(x + 1) ≤ -2
      have h3 : x + 1 ≤ (0 : ℝ) := by
        by_contra h4
        push_neg at h4
        have h4' : x + 1 > (0 : ℝ) := by linarith
        have h4 : f (x + 1) > f (0 : ℝ) := by apply hf.lt_iff_lt.mpr; linarith
        have h5 : f (0 : ℝ) = -2 := hA
        have h7 : f (x + 1) > -2 := by linarith [h4, h5]
        nlinarith
      have h4 : x ≤ -1 := by linarith
      left
      exact h4
    · -- Assume f(x + 1) ≥ 2
      have h3 : x + 1 ≥ (3 : ℝ) := by
        by_contra h4
        push_neg at h4
        have h4' : x + 1 < (3 : ℝ) := by linarith
        have h5 : f (x + 1) < f (3 : ℝ) := by apply hf.lt_iff_lt.mpr; linarith
        have h5' : f (3 : ℝ) = 2 := hB
        have h8 : f (x + 1) < (2 : ℝ) := by linarith [h5, h5']
        nlinarith
      have h4 : x ≥ (2 : ℝ) := by linarith
      right
      linarith
  · -- Assume $x \leq -1$ or $x \geq 2$, we need to show $|f(x + 1)| \geq 2$.
    intro h
    rcases h with (h | h)
    · -- Assume x ≤ -1
      have h1 : x + 1 ≤ (0 : ℝ) := by linarith
      have h2 : f (x + 1) ≤ -2 := by
        have h3 : f (x + 1) ≤ f (0 : ℝ) := by
          apply hf.monotone
          all_goals linarith
        have h4 : f (0 : ℝ) = -2 := hA
        linarith [h3, h4]
      have h2 : abs (f (x + 1)) ≥ 2 := by
        have h3 : f (x + 1) ≤ -2 := h2
        have h4 : abs (f (x + 1)) = -f (x + 1) := by
          rw [abs_of_nonpos (by linarith)]
        linarith [h4, h3]
      linarith
    · -- Assume x ≥ 2
      have h1 : x + 1 ≥ (3 : ℝ) := by linarith
      have h2 : f (x + 1) ≥ 2 := by
        have h3 : f (x + 1) ≥ f (3 : ℝ) := by
          apply hf.monotone
          all_goals linarith
        have h4 : f (3 : ℝ) = 2 := hB
        linarith [h3, h4]
      have h2 : abs (f (x + 1)) ≥ 2 := by
        have h3 : f (x + 1) ≥ 2 := h2
        have h4 : abs (f (x + 1)) = f (x + 1) := by
          rw [abs_of_nonneg (by linarith)]
        linarith [h4, h3]
      linarith