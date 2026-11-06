import Mathlib

theorem number_theory_275876 (n : ℕ) (h : n > 0) :
    6 ∣ 2^n + 2^(n + 1) := by
  have eq1 : 2^n + 2^(n + 1) = 3 * (2^n) := by
    ring_nf
  rw [eq1]
  have h1 : n > 0 := h
  have h2 : n ≥ 1 := by 
    omega
  have h3 : 3 * (2 ^ n) = 6 * (2 ^ (n - 1)) := by
    cases n with
    | zero => 
      all_goals linarith
    | succ n => 
      cases n with
      | zero => 
        all_goals norm_num
      | succ n => 
        simp [pow_succ, pow_zero, mul_add, mul_assoc] at *
        <;> ring_nf
  rw [h3]
  all_goals
    omega