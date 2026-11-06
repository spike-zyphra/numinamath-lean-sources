import Mathlib

theorem number_theory_5103 : IsLeast {z : ℕ | ∃ x y, 0 < x ∧ 0 < y ∧ 7 * x + 6 * y = 249 ∧ z = x + y} 36 := by
  constructor
  · -- Show 36 is in the set
    use 33, 3
    all_goals norm_num
  · -- Show no value less than 36 is in the set
    intro z h
    rcases h with ⟨x, y, hx, hy, heq, hz⟩
    by_contra h'
    push_neg at h'
    have h1 : x + y < (36 : ℕ) := by linarith [hz, h']
    have eq1 : 7 * x + 6 * y = 249 := heq
    have h2 : x ≥ 1 := hx
    have h3 : y ≥ 1 := hy
    have h4 : x ≤ 35 := by
      omega
    have h5 : y ≤ 35 := by
      omega
    interval_cases x <;> omega