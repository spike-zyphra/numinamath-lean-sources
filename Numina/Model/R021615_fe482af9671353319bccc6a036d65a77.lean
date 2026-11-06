import Mathlib

theorem algebra_2890 :
    IsLeast {z : ℤ | ∃ x y : ℤ, x > 0 ∧ y > 0 ∧ 4 * x ^ 2 + 4 * x * y + y ^ 2 + 43 * y - 2022 = 0 ∧ z = x + y} 23 := by
  constructor
  · -- First, show 23 is in the set
    use 21, 2
    all_goals norm_num
  · -- Second, show 23 is the least
    intro z hz
    rcases hz with ⟨x, y, hx1, hy1, heq, hz⟩
    by_contra h
    push_neg at h
    have h4 : x + y ≤ 22 := by
      omega
    have h5 : y ≤ 21 := by
      nlinarith
    interval_cases y <;> try { 
      have : x ≤ 21 := by 
        nlinarith 
      interval_cases x 
      <;> omega 
      <;> norm_num at heq 
      <;> omega 
    }