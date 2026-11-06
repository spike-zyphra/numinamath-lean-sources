import Mathlib

open Nat

theorem number_theory_15009 {f : ℕ → ℕ}
    (hf : ∀ n, IsLeast {x | n ∣ x ! } (f n)) :
    IsLeast {n | 15 ∣ n ∧ f n > 15} 255 := by
  have h1 := hf 0
  have h2 : f 0 ∈ {x | (0 : ℕ) ∣ x ! } := by
    exact h1.left
  simp at h2
  -- h2 is (f 0)! = 0
  -- This is a contradiction because a factorial is always positive
  have h3 : (f 0) ! > 0 := by
    apply Nat.factorial_pos
  linarith