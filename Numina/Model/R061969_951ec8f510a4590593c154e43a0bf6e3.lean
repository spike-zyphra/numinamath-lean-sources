import Mathlib

theorem number_theory_119779 (a b c : ℕ) (h₀ : a ≠ 0) :
    (37 ∣ (100 * a + 10 * b + c)) → (37 ∣ (100 * b + 10 * c + a)) ∧
    (37 ∣ (100 * c + 10 * a + b)) := by
  intro h
  have h1 : 37 ∣ (100 * b + 10 * c + a) := by
    omega
  have h2 : 37 ∣ (100 * c + 10 * a + b) := by
    omega
  exact ⟨h1, h2⟩