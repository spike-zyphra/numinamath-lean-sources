import Mathlib

theorem number_theory_14587 (d1 d2 : ℕ → ℤ)
    (h₀ : ∀ a, d1 a = a ^ 2 + 2 ^ a + a * 2 ^ ((a + 1) / 2))
    (h₁ : ∀ a, d2 a = a ^ 2 + 2 ^ a - a * 2 ^ ((a + 1) / 2)) :
    Set.ncard {a | 1 ≤ a ∧ a ≤ 251 ∧ 5 ∣ d1 a * d2 a} = 101 := by
  have h2 : {a | 1 ≤ a ∧ a ≤ 251 ∧ 5 ∣ d1 a * d2 a} = Finset.filter (fun a => 1 ≤ a ∧ a ≤ 251 ∧ 5 ∣ d1 a * d2 a) (Finset.Icc (0 : ℕ) 251) := by
    ext a
    simp
    <;> omega
  rw [h2]
  rw [Set.ncard_coe_Finset]
  simp [h₀, h₁]
  <;> native_decide