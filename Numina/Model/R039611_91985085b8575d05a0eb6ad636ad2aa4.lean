import Mathlib

open Nat

theorem number_theory_608427 {n : ℕ} (h : n ∣ (n^2 + n + 2)) : n = 1 ∨ n = 2 := by 
  have h1 : n ∣ (n^2 + n + 2) := h
  -- Now, to derive the n | 2 from given hypothesis.
  have h4 : n ∣ (n * (n + 1)) := by
    use (n + 1)
    all_goals ring
  have h5 : n ∣ (n ^ 2 + n + 2 - (n * (n + 1))) := by 
    apply Nat.dvd_sub' 
    · exact h1
    · exact h4 
  have h6 : (n ^ 2 + n + 2 - (n * (n + 1))) = 2 := by 
    cases n with
    | zero =>
      all_goals omega 
    | succ n => 
      simp [Nat.pow_succ, Nat.mul_add, mul_add, add_mul, mul_assoc]
      <;> ring_nf <;> omega 
      all_goals omega 
  -- Now we establish n divides 2 from h4 and h6.
  have h2 : n ∣ 2 := by
    rw [h6] at h5 
    exact h5 
  -- From n divides 2, we know n ≤ 2
  have h7 : n ≤ 2 := by 
    exact Nat.le_of_dvd (show (0 : ℕ) < 2 by norm_num) h2 
    all_goals linarith 
    all_goals linarith
  interval_cases n <;> tauto 
  all_goals linarith