import Mathlib

theorem algebra_14019 :
    IsGreatest {x : ℕ | x.lcm (Nat.lcm 10 14) = 70} 70 := by
  constructor
  · -- Show 70 is in the set 
    show 70 ∈ {x : ℕ | x.lcm (Nat.lcm 10 14) = 70}
    native_decide 
  · -- Show there is no greater element in the set
    intro x hx 
    have h : x ∈ {x : ℕ | x.lcm (Nat.lcm 10 14) = 70} := hx 
    have h1 : x.lcm (Nat.lcm 10 14) = 70 := h 
    have h2 : x ∣ 70 := by
      have h3 : x.lcm (Nat.lcm 10 14) = 70 := h1 
      have h4 : x ∣ x.lcm (Nat.lcm 10 14) := by 
        apply Nat.dvd_lcm_left 
      rw [h3] at h4 
      exact h4 
    have h3 : x ≤ 70 := by 
      exact Nat.le_of_dvd (by norm_num) h2 
    linarith