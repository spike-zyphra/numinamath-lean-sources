import Mathlib

/- Josanna's test scores to date are 90,80,70,60 and 85. Her goal is to raise her test average at least 3 points with 
her next test. What is the minimum test score she would need to accomplish this goal?
(A) 80 (B) 82 (C) 85 (D) 90 (E) 95-/
theorem algebra_94865 : IsLeast {x : ℕ | ((90 + 80 + 70 + 60 + 85 + x) / 6) ≥ ((90 + 80 + 70 + 60 + 85) / 5 + 3)} 95 := by {
  -- To show that 95 is the least x, we need to show that 95 satisfies the inequality and that any x that satisfies it 
  -- is ≥ 95
  constructor
  -- Showing that 95 satisfies it is trivial
  simp
  -- Now we show the other direction
  unfold lowerBounds
  simp
  intros x h
  -- So we need to show that 80 ≤ (385 + x) / 6 implies 95 ≤ x, which follows from simple rearranging.
  apply Nat.mul_le_of_le_div at h
  rw [←Nat.sub_le_iff_le_add'] at h
  norm_num at h
  exact h
}