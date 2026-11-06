import Mathlib

theorem algebra_247087 {p q : ℝ} (hp : p > 0) (hq : q > 0)
    (A1 A2 A3 : ℝ × ℝ)
    (hA1 : A1.1 ^ 2 = 2 * p * A1.2)
    (hA2 : A2.1 ^ 2 = 2 * p * A2.2)
    (hA3 : A3.1 ^ 2 = 2 * p * A3.2)
    (hA12 : A1 ≠ A2)
    (hA13 : A1 ≠ A3)
    (hA23 : A2 ≠ A3)
    (hA123 : A1.1 ^ 2 = 2 * q * (A1.2 + A2.2))
    (hA12' : A1.1 ^ 2 = 2 * q * (A1.2 + A3.2))
    (hA23' : A2.1 ^ 2 = 2 * q * (A2.2 + A3.2)) :
    ∃ c, ∀ i j, i ≠ j ∧ i ∈ Finset.Icc 1 3 ∧ j ∈ Finset.Icc 1 3 →
      A1.2 * A2.2 * (A1.2 + A2.2) = c := by
  use A1.2 * A2.2 * (A1.2 + A2.2)
  intro i j h
  rcases h with ⟨hne, hi, hj⟩
  fin_cases hi <;> fin_cases hj <;> simp at *
  <;> try { tauto }