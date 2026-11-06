import Mathlib

/- define the answer to the problem -/
abbrev Solution_4853 : ℕ → ℕ := fun n => match n with
  | 13 => 12
  | 14 => 6
  | 15 => 8
  | 16 => 8
  | 17 => 16
  | 18 => 6
  | 19 => 18
  | 20 => 8
  | _ => 0

theorem number_theorey_4853 : ∀ n, 13 ≤ n ∧ n ≤ 20 → (Nat.totient n = Solution_4853 n) := by
  intro n hn
  rcases hn with ⟨h₃, h₄⟩
  interval_cases n <;> try { 
    native_decide 
  }
  <;> try { 
    rfl 
  }