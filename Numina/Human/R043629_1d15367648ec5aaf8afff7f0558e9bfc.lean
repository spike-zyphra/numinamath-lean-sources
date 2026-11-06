import Mathlib

theorem algebra_92294 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h : l' = l * 1.1 ∧ w' = w * 1.1) :
    (2 * (l' + w')) / (2 * (l + w)) = 1.1 := by 
  rcases h with ⟨hl', hw'⟩
  field_simp
  rw [hl', hw']
  ring