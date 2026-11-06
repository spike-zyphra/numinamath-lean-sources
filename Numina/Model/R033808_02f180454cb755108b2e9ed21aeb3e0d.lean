import Mathlib
import Mathlib.Tactic.Linarith


theorem algebra_708 :
    (∃ m n : ℕ, 2 * m * n * 130 = (m + 2) * (n + 2) * (130 + 2)) ∧
    (∀ p : ℕ, (∃ m n : ℤ, 0 ≤ m ∧ 0 ≤ n ∧ 2 * m * n * p = (m + 2) * (n + 2) * (p + 2))
    → p ≤ 130) := by 
  constructor
  · -- Show the existence part.
    use 3, 11
    all_goals
      norm_num
  · -- Show the forall part.
    intro p
    intro h
    rcases h with ⟨m, n, hm, hn, heq⟩
    by_contra h'
    push_neg at h'
    have eq4 : (p : ℤ) ≥ 131 := by omega
    have h66 : (m + 2 : ℤ) * (n + 2) * (p + 2) ≥ 0 := by nlinarith
    have h666 : (m : ℤ) ≥ 0 := by linarith
    have h777 : (n : ℤ) ≥ 0 := by linarith
    have h888 : (p : ℤ) ≥ 0 := by linarith
    have h66 : (m - 2 : ℤ) * (n - 2) ≥ 9 := by
      nlinarith [sq_nonneg ((m : ℤ) - 2), sq_nonneg ((n : ℤ) - 2), sq_nonneg ((m : ℤ) - (n : ℤ)), sq_nonneg ((m : ℤ) - (n : ℤ) + 4)]
    have h77 : (m - 2 : ℤ) ≥ 1 := by nlinarith
    have h100 : (n - 2 : ℤ) ≥ 1 := by nlinarith
    have h88 : (m : ℤ) ≥ 3 := by nlinarith
    have h99 : (n : ℤ) ≥ 3 := by nlinarith
    have h1000 : (m : ℤ) ≤ 30 := by
      nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), sq_nonneg ((m : ℤ) - (n : ℤ) + 4)]
    have h1011 : (n : ℤ) ≤ 30 := by
      nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ)), sq_nonneg ((m : ℤ) - (n : ℤ) + 4)]
    interval_cases m <;> interval_cases n
    <;> omega