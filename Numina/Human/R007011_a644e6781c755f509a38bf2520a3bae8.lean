import Mathlib

/- What is the smallest positive integer that satisfies the congruence $30x \equiv 42 \pmod{47}$? -/
theorem number_theory_19176 : IsLeast {x : ℕ | 0 < x ∧ 30 * x ≡ 42 [MOD 47]} 39 := by 
  refine' ⟨by decide, fun x => _⟩
  simp [Nat.ModEq]
  exact fun hx => by omega