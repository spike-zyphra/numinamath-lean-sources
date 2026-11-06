import Mathlib
set_option maxHeartbeats 0

open Finset

/-An electric cable 21 meters long is cut into 21 pieces. For any two pieces, their lengths differ by no more than a factor of three. What is the smallest $m$ such that there will definitely be two pieces whose lengths differ by no more than a factor of $m$?-/
theorem number_theory_200354 : IsLeast {t | ∃ l : ℕ → ℝ, (∀ i ∈ range 21, 0 < l i) ∧
    ∑ i ∈ range 21, l i = 21 ∧ (∀ i ∈ range 21, ∀ j ∈ range 21, 1 / 3 ≤ l i / l j ∧ l i / l j ≤ 3) ∧
    ∃ i ∈ range 21, ∃ j ∈ range 21, i ≠ j ∧ 1 / t ≤ l i / l j ∧ l i / l j ≤ t} 1 := by
  simp [IsLeast, lowerBounds]; constructor
  -- Fulfill the goal with a constant series $l_i = 1$, it is straightforward to check that required conditions are satisfied
  · let l : ℕ → ℝ := fun _ => 1
    use l; simp [l]; constructor
    · intros; norm_num
    use 0; norm_num
    use 1; norm_num
-- Prove that $1$ is a lower bound of the set in question
  intro a l lpos lsum hdiff i ilt j jlt inej ale lea
  have apos : 0 < a := by calc
    _ < l i / l j := by
      apply div_pos
      all_goals apply lpos; assumption
    _ ≤ _ := lea
  replace lea := le_trans ale lea
  rw [inv_le_iff_one_le_mul₀, ← pow_two] at lea
  rw [one_le_sq_iff₀] at lea; exact lea
  all_goals positivity

