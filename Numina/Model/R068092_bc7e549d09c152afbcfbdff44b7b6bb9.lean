import Mathlib

def f (x : ℕ) := x % 3
def g (y : ℕ) := y % 4

theorem number_theory_316898 :
    IsGreatest {z | ∃ x y, x ∈ Finset.Icc 1 10 ∧ y < 10 ∧ f x + 2 * g y = 0 ∧ z = x + 2 * y} 25 := by 
  constructor
  · -- Show 25 is in the set
    use 9, 8
    simp [f, g, Finset.mem_Icc]
    <;> try { all_goals omega }
  · -- Show no element greater than 25 exists in the set
    intro z h
    rcases h with ⟨x, y, hx1, hy1, h_eq, hz⟩
    simp only [Finset.mem_Icc] at hx1 ⊢
    rcases hx1 with ⟨hx1_lower, hx1_upper⟩
    simp [f, g] at h_eq
    -- Now we have arithmetic expression with % operators which omega does not understand.
    -- So we need to do interval_cases for x and y.
    interval_cases x <;> interval_cases y <;> norm_num at h_eq hz 
      <;> omega