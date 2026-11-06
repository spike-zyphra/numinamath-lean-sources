import Mathlib

theorem algebra_13605 : IsGreatest {z | ∃ (a b : ℕ) (_ : a > 0) (_ : b > 0) (_ : 2 * (a + b) = 142), z = a * b} 1260 := by 
  constructor
  · -- Show 1260 is in the set
    use 35, 36
    all_goals norm_num
  · -- Show no greater value is in the set
    intro z h
    rcases h with ⟨a, b, ha, hb, h1, hz⟩
    -- From 2*(a+b)=142 we get a+b=71
    have h2 : a + b = 71 := by
      omega
    have h3 : b = 71 - a := by 
      omega 
    rw [hz, h3]
    have h4 : a ≤ 71 := by 
      omega
    interval_cases a <;> omega