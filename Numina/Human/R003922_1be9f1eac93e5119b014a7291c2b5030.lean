import Mathlib

set_option maxRecDepth 2000

theorem number_theory_222434
  (S : Set (ℕ × ℕ × ℕ))
  (hS : S = {(a, b, c) : ℕ × ℕ × ℕ | a.lcm b = 1000 ∧ b.lcm c = 2000 ∧ c.lcm a = 2000}) :
  S.ncard = 70 := by

  have : S = Finset.filter (fun s : ℕ × ℕ × ℕ => (s.1).lcm (s.2.1) = 1000 ∧ (s.2.1).lcm (s.2.2) = 2000 ∧ (s.2.2).lcm (s.1) = 2000) ((Nat.divisors 1000) ×ˢ (Nat.divisors 1000) ×ˢ (Nat.divisors 2000)) := by
    ext ⟨a, b, c⟩
    rw [hS]
    simp
    intro hab hbc hca
    refine ⟨?_, ?_, ?_⟩
    . rw [← hab]
      exact dvd_lcm_left a b
    . rw [← hab]
      exact dvd_lcm_right a b
    . rw [← hca]
      exact dvd_lcm_left c a

  rw [this]
  norm_cast
