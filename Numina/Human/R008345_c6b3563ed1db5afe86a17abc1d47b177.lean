import Mathlib

/- Find the smallest positive integer $n$ such that $$ 617n \equiv 943n \pmod{18}. $$ -/
theorem number_theory_23002 :
    IsLeast {n : ℕ | 0 < n ∧ (617 * n ≡ 943 * n [MOD 18])} 9 := by 
  refine' ⟨by decide, _⟩
  intro n hn
  simp [Nat.ModEq] at hn
  omega