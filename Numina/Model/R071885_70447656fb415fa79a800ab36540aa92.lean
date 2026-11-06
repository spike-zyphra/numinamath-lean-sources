import Mathlib

theorem number_theory_19163 (n : ℕ) (h : n % 7 = 2) :
    (n + 2) * (n + 4) * (n + 6) ≡ 3 [MOD 7] := by
  simp [Nat.ModEq] at h ⊢ -- Simplify the goal using the modular equivalence definition
  have h2 : (n + 2) % 7 = 4 := by
    omega -- Arithmetic solver in Lean for integer arithmetic
  have h3 : (n + 4) % 7 = 6 := by
    omega -- Solves integer arithmetic goals
  have h4 : (n + 6) % 7 = 1 := by
    omega -- Solves integer arithmetic goals
  simp [Nat.mul_mod, h2, h3, h4]
  all_goals try omega