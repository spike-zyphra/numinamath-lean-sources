import Mathlib

open Nat

/-- Show that for any integer $n \geq 2$, you can find $n$ consecutive integers such that none of them is prime. -/
theorem number_theory_4210 {n : ℕ} : ∃ k, ∀ i ∈ Finset.Ico k (k+n), ¬Nat.Prime i := by
  -- let $k = \left(n+1\right)! + 2$
  use (n+1)! + 2
  intro i hi
  simp at hi
  -- Exists $k \in \left[1,n \right]$, $i = (n+1)! + 1 + k$
  have hi' : ∃ k ∈ Finset.Icc 1 n, i = (n + 1)! + 1 + k := by
    use i - ((n + 1)! + 1)
    simp_all
    constructor
    · constructor
      · rcases hi with ⟨hi, hi'⟩
        rw [(show 2 = 1 + 1 by ring), ← add_assoc, add_comm] at hi
        apply Nat.le_sub_of_add_le hi
      · nlinarith
    · calc
        i = i + (n + 1)! - (n + 1)! + 1 - 1 := by aesop
        _ = ((n + 1)! + i - (n + 1)! - 1) + 1 := by
          rw [add_comm i,Nat.sub_add_comm]
          simp_all; linarith
        _ = ((n + 1)! + (i - (n + 1)! - 1)) + 1 := by
          rw [Nat.add_sub_assoc _ (n + 1)!,Nat.add_assoc,Nat.add_sub_assoc]
          rw [Nat.add_assoc]
          rcases hi with ⟨hi, hi'⟩
          rw [Nat.add_comm] at hi
          apply Nat.le_sub_of_add_le
          have : 1 + (n + 1)! ≤ 2 + (n + 1)! := by linarith
          apply le_trans this hi
          have : (n + 1)! ≤ (n + 1)! + 2 := by linarith
          rcases hi with ⟨hi, _⟩
          apply le_trans this hi
        _ = (n + 1)! + 1 + (i - ((n + 1)! + 1)) := by
          rw [add_right_comm, Nat.sub_add_eq]
  rcases hi' with ⟨k, _, hik⟩
  rw [hik]
  have hdvd : k + 1∣((n + 1)! + 1 + k) := by
    rw [add_assoc]
    have h : k + 1 ∣ (n + 1)! := Nat.dvd_factorial (by linarith) (by nlinarith)
    have h' : k + 1 ∣ 1 + k := by rw [add_comm]
    apply Nat.dvd_add h h'
  have h₂ : 2 ≤ k + 1 := by linarith
  have h₃ : k + 1 < (n + 1)! + 1 + k := by
    have : 0 < (n + 1)! := Nat.factorial_pos (n + 1)
    linarith
  apply Nat.not_prime_of_dvd_of_lt hdvd h₂ h₃
