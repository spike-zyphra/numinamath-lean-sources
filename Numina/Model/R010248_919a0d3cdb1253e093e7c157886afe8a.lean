import Mathlib

theorem number_theory_4639
(m : ℕ) (_ : 0 < m) :
(∀ a : ℤ, a ≡ a [ZMOD m]) ∧
(∀ a b : ℤ, a ≡ b [ZMOD m] → b ≡ a [ZMOD m]) ∧
(∀ a b c : ℤ, a ≡ b [ZMOD m] → b ≡ c [ZMOD m] → a ≡ c [ZMOD m]) := by 
  constructor
  · -- Proof of reflexivity
    intro a
    exact Int.ModEq.refl a
  constructor
  · -- Proof of symmetry
    intros a b h
    exact Int.ModEq.symm h
  · -- Proof of transitivity
    intros a b c h1 h2
    exact Int.ModEq.trans h1 h2