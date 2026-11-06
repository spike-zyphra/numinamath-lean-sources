import Mathlib

open Nat

theorem algebra_129196 (x : ℕ) (hx : x > 0) : x ! = (x:ℤ) ^ 3 - 11 * x + 4 ↔ x = 4 := by 
  constructor
  
  intro h

  --We first prove that if x≥ 5, then the x ! is too large such that the assumption cannot hold.
  have : x ≤ 4 := by 
    by_contra
    have xge5 : 5 ≤ x := by omega
    by_cases hx : x = 5
    rw [hx] at h
    simp at h
    have : 5 ! = 120 := by simp [Nat.factorial]
    rw [this] at h
    norm_num at h

    have : 6 ≤ x := by omega

    have cla : (x !) >  ((x:ℤ) ^ 3 - 11 * x + 4) := by 
      have ind: ∀ n : ℕ, ((n+6) !) >  (((n+6):ℤ) ^ 3 + 4) := by 
        intro n
        induction' n with n hn
        simp
        have : 6! = 720 := by simp [Nat.factorial]
        rw [this]
        norm_num
        
        have t1 : (n+6+1)! = (↑(n+6+1) * ↑((n+6)!)) := Eq.symm (Nat.factorial_succ (n+6))
        rw [t1]
        norm_cast
        nlinarith




      have exi : ∃ n : ℕ, n+6 = x := by use x-6; omega
      obtain ⟨n,hn⟩ := exi
      rw [←hn]
      have : @Nat.cast ℤ instNatCastInt (n + 6)! > (@Nat.cast ℤ instNatCastInt (n + 6)) ^ 3 + 4 := by apply ind n
      linarith
      
    
    linarith

  --As a result, x can only by 1 or 2 or 3 or 4.
  by_cases xe4 : x = 4
  exact xe4
  by_cases xe3 : x = 3
  exfalso
  rw [xe3] at h
  norm_cast at h
  by_cases xe2 : x = 2
  exfalso
  rw [xe2] at h
  norm_cast at h
  have xe1 : x = 1 := by omega
  exfalso
  rw [xe1] at h
  norm_cast at h
  
  --To verify that 4 is a solution. Just simple calculation.
  intro xeq
  rw [xeq]
  norm_cast
