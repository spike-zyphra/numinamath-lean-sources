import Mathlib

/- Find the largest number $n$ such that (2004!)! is divisible by (( $n!)!$ )!.-/
theorem number_theory_611192 :
    IsGreatest {n | (Nat.factorial (Nat.factorial (Nat.factorial n))) ∣ Nat.factorial (Nat.factorial 2004)} 6 := by
  -- Prove tha a! ∣ b! ↔ a ≤ b.
  have h₀ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : Nat.factorial a ∣ Nat.factorial b ↔ a ≤ b := by
    apply Iff.intro
    . intro h
      by_contra!
      have h' := le_of_lt this
      apply Nat.factorial_dvd_factorial at h'
      have h'' := Nat.dvd_antisymm h h'
      rw [Nat.factorial_inj] at h''
      linarith
      omega
    . intro h
      apply Nat.factorial_dvd_factorial h
  -- Prove that a! ≤ b! ↔ a ≤ b.
  have h₁ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : a.factorial ≤ b.factorial ↔ a ≤ b := by
    apply Iff.intro
    . intro h
      by_contra!
      have h' := le_of_lt this
      apply Nat.factorial_dvd_factorial at h'
      apply Nat.le_of_dvd at h'
      replace h : a.factorial = b.factorial := by linarith
      rw [Nat.factorial_inj] at h
      linarith
      omega
      positivity
    . intro h
      exact Nat.factorial_le h
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds]
  rw [h₀, h₁]
  refine ⟨?_, ?_⟩
  . -- We have 6! ≤ 2004.
    simp [Nat.factorial]
  . intro a h
    rw [h₀, h₁] at h
    -- We have a! ≤ 2004, hence a ≤ 6.
    by_contra!
    replace this : 7 ≤ a := by omega
    rw [<-h₀] at this
    simp [Nat.factorial] at this
    apply Nat.le_of_dvd at this
    linarith
    all_goals
      positivity
  all_goals
    positivity
