import Mathlib

/- What is the smallest positive integer $n$ such that $531n \equiv 1067n \pmod{24}?$ -/
theorem number_theory_16151 : IsLeast {n : ℕ | 0 < n ∧ (531 * n ≡ 1067 * n [MOD 24])} 3 := by
  refine ⟨?_, fun n hn => ?_⟩ <;> simp_all [Nat.ModEq, Nat.ModEq]
  <;> omega