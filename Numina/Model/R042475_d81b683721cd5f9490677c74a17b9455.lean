import Mathlib

theorem number_theory_74223 (n : ℕ) (hn : n > 0)
    (h : ∀ i ∈ Finset.range 35, Nat.gcd n (n + i + 1) < Nat.gcd n (n + i + 2)) :
    Nat.gcd n (n + 35) < Nat.gcd n (n + 36) := by 
  have h34 : 34 ∈ Finset.range 35 := by 
    simp [Finset.mem_range]
    all_goals omega
  have h34' : Nat.gcd n (n + 34 + 1) < Nat.gcd n (n + 34 + 2) := by
    apply h 34 h34
  have h'1 : Nat.gcd n (n + 34 + 1) = Nat.gcd n (n + 35) := by 
    ring_nf
  have h'2 : Nat.gcd n (n + 34 + 2) = Nat.gcd n (n + 36) := by 
    ring_nf
  rw [h'1, h'2] at h34'
  exact h34'