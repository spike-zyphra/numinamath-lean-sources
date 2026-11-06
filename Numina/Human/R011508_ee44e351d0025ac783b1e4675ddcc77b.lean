import Mathlib


/- Given that the solution set of the inequality $\frac{ax-5}{{{x}^{2}}-a}<{}0$ is $M$,
if $2$ and $-1$ have exactly one that is not in $M$, find the range of the real number $a$. -/
theorem algebra_622181 {M: Set ℝ} {a:ℝ}
  (hM: M = {x:ℝ | (a*x-5) / (x^2-a) < 0}):
  ( (2 ∈ M ∧ -1 ∉ M) ∨ (2 ∉ M ∧ -1 ∈ M) ) ↔
  (a ≤ -5 ∨ a ∈ Set.Ico 1 (5/2) ∨ a > 4) := by

  -- cannot be the case 2 not in M but -1 in M.
  have: ¬ (2 ∉ M ∧ -1 ∈ M) := by
    simp only [hM, Set.mem_setOf_eq, mul_neg, mul_one,
    even_two, Even.neg_pow, one_pow, not_lt, not_and, not_le]
    intro h
    rw [div_nonneg_iff] at h
    rcases h with h | h
    · apply div_nonneg_of_nonpos
      <;> linarith only [h.left]
    · absurd h
      push_neg
      intro hh
      linarith only [hh]
  simp only [this, or_false]

  -- then it suffices to solve a from 2 in M and -1 not in M.
  simp only [hM, Set.mem_setOf_eq, mul_neg, mul_one, even_two,
  Even.neg_pow, one_pow, not_lt, Set.mem_Ico, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_neg_iff] at h1
    rw [div_nonneg_iff] at h2
    rcases h1 with h1 | h1
    · right; right
      linarith only [h1.right]
    · rcases h2 with h2 | h2
      · left; linarith only [h2.left]
      · right; left
        constructor <;> linarith only [h2.right, h1.left]
  · rintro (ha | ha | ha)
    <;> constructor
    · apply div_neg_of_neg_of_pos <;> linarith only [ha]
    · apply div_nonneg <;> linarith only [ha]
    · apply div_neg_of_neg_of_pos <;> linarith only [ha.right]
    · apply div_nonneg_of_nonpos <;> linarith only [ha.left]
    · apply div_neg_of_pos_of_neg <;> linarith only [ha]
    · apply div_nonneg_of_nonpos <;> linarith only [ha]