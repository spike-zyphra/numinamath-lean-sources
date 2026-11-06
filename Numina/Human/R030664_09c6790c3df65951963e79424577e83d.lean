import Mathlib

/- Which of the following expressions is never a prime number when p is a prime number?
(A) p^2 + 16 (B) p^2 + 24 (C) p^2 + 26 (D) p^2 + 46 (E) p^2 + 96-/
theorem number_theory_96872 (p : ℕ) (hp : Nat.Prime p) :
¬ Nat.Prime (p ^ 2 + 26) := by {
  -- We will assume that p^2 + 26 is a prime and show that it implies False.
  intro h
  -- First of all, we will exclude the case p = 3, which evaluates to 35, thus not a prime.
  have h3 : p ≠ 3 := by {
    intro hp3
    rw [hp3] at h
    norm_num at h
  }

  suffices : 3 ∣ (p ^ 2 + 26)

  -- We now show that it suffices to prove that 3 | (p ^ 2 + 26). This is because since we assume that it is a prime,
  -- we must have 3 = p ^ 2 + 26, which is impossible.
  apply Nat.prime_dvd_prime_iff_eq (Nat.prime_three) at h
  rw [h] at this
  suffices : 26 ≤ 3
  trivial
  calc 26 ≤ p^2 + 26 := by {apply Nat.le_add_left}
       _ = 3 := by rw [this]
  

  -- Now we prove that we always have 3 | (p ^ 2 + 26). We do this by case distinction according to p % 3.
  mod_cases h : p % 3
  
  -- The case p % 3 = 0 is obvious since we already excluded p = 3.
  unfold Nat.ModEq at h
  simp at h
  rw [←Nat.dvd_iff_mod_eq_zero,Nat.dvd_prime hp] at h
  simp at h
  rw [←h] at h3
  trivial

  -- In the other two cases, this follows from simple modular arithmetic, since we must have p^2 % 3 = 1.
  have h₁ : p ^ 2 + 26 ≡ 0 [MOD 3] := by {
    calc p^2 + 26 ≡ 1 ^ 2 + 26 [MOD 3] := by {
      rw [←Int.natCast_modEq_iff,Int.natCast_add,Int.natCast_add] 
      apply Int.ModEq.add_right
      rw [Int.natCast_pow,Int.natCast_pow]
      apply Int.ModEq.pow
      rw [Int.natCast_modEq_iff]
      exact h
      }
  }
  rw [Nat.dvd_iff_mod_eq_zero]
  exact h₁

  have h₂ : p ^ 2 + 26 ≡ 0 [MOD 3] := by {
    calc p^2 + 26 ≡ 2 ^ 2 + 26 [MOD 3] := by {
      rw [←Int.natCast_modEq_iff,Int.natCast_add,Int.natCast_add] 
      apply Int.ModEq.add_right
      rw [Int.natCast_pow,Int.natCast_pow]
      apply Int.ModEq.pow
      rw [Int.natCast_modEq_iff]
      exact h
      }
  }
  rw [Nat.dvd_iff_mod_eq_zero]
  exact h₂
}