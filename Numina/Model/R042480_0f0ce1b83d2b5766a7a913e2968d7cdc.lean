import Mathlib

open Nat

theorem number_theory_1233 (p : ℕ) (hp : Nat.Prime p) :
    ∃ n, n^2 = p^4 + p^3 + p^2 + p + 1 ↔ p = 3 := by 
  by_cases h : p = 3 
  · -- p = 3, then there exists n=11 s.t. ... 
    use 11 
    simp [h]
  · -- Assume p ≠ 3. 
    by_cases h1 : p ≤ 3 
    · -- p ≤ 3 and p ≠ 3. As p is prime, p=2
      have h2 : p = 2 := by 
        interval_cases p <;> norm_num at h1 hp h <;> tauto
      use 5 
      simp [h2]
    · -- p > 3
      have h11 : p > 3 := by
        omega 
      use 0 
      have hp2 : p > 0 := by
        by_contra hneg
        push_neg at hneg
        have : p = 0 := by
          linarith 
        rw [this] at hp 
        contradiction
      have h111 : p ^ 4 + p ^ 3 + p ^ 2 + p + 1 > 0 := by
        nlinarith [show 0 < p by linarith]
      simp at *
      all_goals
        nlinarith