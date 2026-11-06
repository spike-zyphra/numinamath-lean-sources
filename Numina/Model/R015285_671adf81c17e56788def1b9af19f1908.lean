import Mathlib

theorem number_theory_160898 (x : ℚ) :
    ∃ a : ℕ, 1 ≤ a ∧ x ^ ⌊x⌋ = a / 2 ↔ x = 3 / 2 := by
  by_cases h : x = 3 / 2
  · -- Assume x = 3/2, so that we can prove that a = 3 works
    use 3
    rw [h]
    norm_num
  · -- Assume x ≠ 3/2, so we need to make the left side of the iff false
    use 0
    simp at *
    <;> try { 
      tauto 
    }