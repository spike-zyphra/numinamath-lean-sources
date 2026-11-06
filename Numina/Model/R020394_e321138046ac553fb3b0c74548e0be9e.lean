import Mathlib

open Real
open scoped BigOperators

theorem number_theory_262984 (δ : ℕ → ℕ)
  (hδ : ∀ n, Odd (δ n) ∧ δ n ∣ n ∧ ∀ m, Odd m → m ∣ n → m ≤ δ n) :
  ∀ x > 0, |∑ i in Finset.Icc 1 x, (δ i : ℚ)/i - 2/3 * x| < 1 := by
  have h1 := hδ 0
  rcases h1 with ⟨h_odd, h_dvd, h_forall⟩
  have h2 := h_forall (δ 0 + 2) (by
    have : Odd (δ 0 + 2) := by
      rcases h_odd with ⟨k, hk⟩
      use k + 1
      omega
    exact this
  ) (by
    simp
  )
  have h3 : δ 0 + 2 ≤ δ 0 := by
    omega
  omega