import Mathlib


open Set


theorem number_theory_34824 {A : Set ℤ} (hA : {t : ℤ | ∃ a b, a > 1 → b > 1 → t = 2 ^ a - 2 ^ b} ⊆ A)
    (hA' : ∀ a b : ℤ, a ∈ A → b ∈ A → a + b ∈ A) (hodd : ∃ x, x ∈ A ∧ Odd x) : A = Set.univ := by
  have h1 : ∀ (t : ℤ), t ∈ {t : ℤ | ∃ a b, a > 1 → b > 1 → t = 2 ^ a - 2 ^ b} := by
    intro t
    use 1, 1
    all_goals
      simp
  have h2 : ∀ (t : ℤ), t ∈ A := by
    intro t
    have h3 : t ∈ {t : ℤ | ∃ a b, a > 1 → b > 1 → t = 2 ^ a - 2 ^ b} := h1 t
    have h4 : t ∈ A := hA h3
    simpa using h4
  ext t
  simp [h2]