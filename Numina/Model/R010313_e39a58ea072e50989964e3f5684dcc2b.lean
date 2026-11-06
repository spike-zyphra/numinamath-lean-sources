import Mathlib

theorem number_theory_4643
(a b c d m : ℤ)
(h₀ : m > 0)
(h₁ : a ≡ b [ZMOD m])
(h₂ : c ≡ d [ZMOD m]) :
a + c ≡ b + d [ZMOD m] ∧ a - c ≡ b - d [ZMOD m] ∧ a * c ≡ b * d [ZMOD m] := by
  constructor
  · -- Proof of (i) a + c ≡ b + d (mod m)
    exact Int.ModEq.add h₁ h₂
  constructor
  · -- Proof of (ii) a - c ≡ b - d (mod m)
    exact Int.ModEq.sub h₁ h₂
  · -- Proof of (iii) a * c ≡ b * d (mod m)
    exact Int.ModEq.mul h₁ h₂