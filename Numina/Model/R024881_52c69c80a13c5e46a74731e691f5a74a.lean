import Mathlib

theorem number_theory_276403 (x y z : ℕ) (h₀ : x > y) (h₁ : y > z)
    (h₂ : Nat.lcm x y = 200) (h₃ : Nat.lcm y z = 300) (h₄ : Nat.lcm x z = 120) :
    x = 40 ∧ y = 25 ∧ z = 12 := by
  have h5 : x ∣ 200 := by 
    have h6 : x ∣ Nat.lcm x y := by 
      exact Nat.dvd_lcm_left x y
    rw [h₂] at h6 
    exact h6
  have h6 : x ∣ 120 := by
    have h7 : x ∣ Nat.lcm x z := by
      exact Nat.dvd_lcm_left x z
    rw [h₄] at h7 
    exact h7
  have h7 : x ∣ 40 := by
    exact Nat.dvd_gcd h5 h6
  have h8 : x ≤ 40 := by
    exact Nat.le_of_dvd (by omega) h7
  have h9 : y ∣ 300 := by
    have h10 : y ∣ Nat.lcm y z := by 
      exact Nat.dvd_lcm_left y z
    rw [h₃] at h10 
    exact h10
  have h10 : z ∣ 300 := by
    have h11 : z ∣ Nat.lcm y z := by
      exact Nat.dvd_lcm_right y z
    rw [h₃] at h11 
    exact h11
  have h11 : z ∣ 120 := by
    have h12 : z ∣ Nat.lcm x z := by
      exact Nat.dvd_lcm_right x z
    rw [h₄] at h12 
    exact h12
  have h12 : z ≤ 120 := by
    exact Nat.le_of_dvd (by omega) h11
  interval_cases x <;> try { 
    omega 
  } <;> try { 
    interval_cases y <;> try { 
      omega 
    } <;> try { 
      interval_cases z <;> norm_num [Nat.lcm] at h₂ h₃ h₄ ⊢ 
      <;> tauto 
    }
  }