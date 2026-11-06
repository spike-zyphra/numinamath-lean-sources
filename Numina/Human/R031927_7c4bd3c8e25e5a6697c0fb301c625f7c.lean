import Mathlib

theorem number_theory_112197 (a b c : ℕ) (p : ℕ) (hp : p = 100 * a + 10 * b + c)
    (hdiv : 37 ∣ p) :
    37 ∣ 100 * b + 10 * c + a ∧ 37 ∣ 100 * c + 10 * a + b := by
  rw [hp] at hdiv
  have h1 : 37 ∣ 100 * b + 10 * c + a := by
    omega
  have h2 : 37 ∣ 100 * c + 10 * a + b := by
    omega
  exact ⟨h1, h2⟩