import Mathlib

theorem number_theory_131899 (a b : ℤ) (ha : ¬ ∃ n, n^2 = a) (hb : ¬ ∃ n, n^2 = b) :
    ∃ x y z w : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      x^2 - a * y^2 - b * z^2 + a * b * w^2 = 0 ↔
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x^2 - a * y^2 - b * z^2 = 0 := by
  by_cases h : ∃ x y z, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 - a * y ^ 2 - b * z ^ 2 = 0
  · -- if right side is true, then left side is also true
    rcases h with ⟨x, y, z, h1, h2⟩
    use x, y, z, (0 : ℤ)
    constructor
    · -- Assume left side, prove right side
      intro h
      rcases h with ⟨hne, heq⟩
      exact ⟨x, y, z, h1, by nlinarith⟩
    · -- Assume right side, prove left side
      intro h'
      rcases h' with ⟨x', y', z', hne', heq'⟩
      have hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := h1
      have heq : x ^ 2 - a * y ^ 2 - b * z ^ 2 = 0 := h2
      simp [heq] at *
      tauto
  · -- if right side is false, prove left side is also false
    push_neg at h
    use 0, 0, 0, 0
    simp at h ⊢
    all_goals
      try { tauto }