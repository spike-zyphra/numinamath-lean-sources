import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_311666 (y : ℝ → ℝ)
  (hy : y = λ x => x^2 / 10 - x / 10 + 9 / 5) :
  {x | y x ≤ abs x} =
  {x | 2 ≤ x ∧ x ≤ 9} ∪ {x | -6 ≤ x ∧ x ≤ -3} := by
  ext x
  simp [hy]
  constructor
  · -- Forward: if $y(x) \leq |x|$, then $x \in \{x | 2 \leq x \land x \leq 9\} \cup \{x | -6 \leq x \land x \leq -3\}$
    intro h
    by_cases h1 : x ≥ 0
    · -- x ≥ 0, so |x| = x
      have h2 : abs x = x := abs_of_nonneg (show (0 : ℝ) ≤ x by linarith)
      rw [h2] at h
      have h3 : 2 ≤ x ∧ x ≤ 9 := by
        constructor
        · -- Prove $2 \leq x$
          nlinarith
        · -- Prove $x \leq 9$
          nlinarith
      left
      exact h3
    · -- x < 0, so |x| = -x
      have h2 : abs x = -x := abs_of_neg (show (x : ℝ) < 0 by linarith)
      rw [h2] at h
      have h4 : -6 ≤ x ∧ x ≤ -3 := by
        constructor
        · -- Prove -6 ≤ x
          nlinarith
        · -- Prove x ≤ -3
          nlinarith
      right
      exact h4
  · -- Backward: if $x \in \{x | 2 \leq x \land x \leq 9\} \cup \{x | -6 \leq x \land x \leq -3\}$, then $y(x) \leq |x|$
    rintro (h | h)
    · -- x ∈ {x | 2 ≤ x ∧ x ≤ 9}
      rcases h with ⟨h1, h2⟩
      have h3 : x ≥ 0 := by linarith
      have h4 : abs x = x := abs_of_nonneg (show (0 : ℝ) ≤ x by linarith)
      rw [h4]
      nlinarith
    · -- x ∈ {x | -6 ≤ x ∧ x ≤ -3}
      rcases h with ⟨h1, h2⟩
      have h3 : x < (0 : ℝ) := by linarith
      have h4 : abs x = -x := abs_of_neg (show (x : ℝ) < 0 by linarith)
      rw [h4]
      nlinarith