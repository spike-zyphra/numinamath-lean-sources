import Mathlib

/-
If the least common multiple of $A$ and $B$ is $120$, and the ratio of $A$ to $B$ is $3:4$, then what is their greatest common divisor?
-/


set_option maxHeartbeats 300000
theorem number_theory_16337 {A B : ℕ} (h₀ : Nat.lcm A B = 120) (h₁ : A * 4 = B * 3) :
    Nat.gcd A B = 10 := by
  have h2 : A ∣ 120 := by
    have h2 : A ∣ Nat.lcm A B := by
      exact Nat.dvd_lcm_left A B
    rw [h₀] at h2
    exact h2
  have h3 : B ∣ 120 := by
    have h3 : B ∣ Nat.lcm A B := by
      exact Nat.dvd_lcm_right A B
    rw [h₀] at h3
    exact h3
  have h4 : A ≤ 120 := by
    exact Nat.le_of_dvd (by norm_num) h2
  have h5 : B ≤ 120 := by
    exact Nat.le_of_dvd (by norm_num) h3
  interval_cases A <;> try { 
    omega 
  } 
  <;> try { 
    interval_cases B <;> norm_num [Nat.lcm, Nat.gcd] at h₀ ⊢ <;> omega 
  }