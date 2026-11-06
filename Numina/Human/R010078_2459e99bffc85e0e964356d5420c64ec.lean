import Mathlib

/- What is the smallest positive integer $n$ such that $3n \equiv 1356 \pmod{22}?$ -/
theorem number_theory_16177 : IsLeast {n | 0 < n ∧ 3 * n ≡ 1356 [MOD 22]} 12 := by
  refine' ⟨by decide, fun n hn => _⟩
  simp_all [Nat.ModEq]
  omega