import Mathlib

/- What is the unique three-digit positive integer $x$ satisfying $$100x\equiv 1\pmod{997}~?$$ -/
theorem number_theory_18978 (x : ℕ) (hx : x ∈ Finset.Icc 100 999) :
    100 * x ≡ 1 [MOD 997] ↔ x = 668 := by
  simp [Nat.ModEq]
  norm_num at hx
  omega