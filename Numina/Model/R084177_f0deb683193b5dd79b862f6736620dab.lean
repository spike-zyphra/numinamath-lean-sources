import Mathlib

theorem algebra_324895 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x : ℕ → ℝ) (h : ∀ i ∈ Finset.range n, x i = a + b / x ((i + n - 1) % n)) :
    Odd n → ∀ i ∈ Finset.range n, x i = x 0 ∧ Even n → ∀ i ∈ Finset.range n,
      x i = if i % 2 = 0 then x 0 else x 1 := by
  intro hn i hi h_absurd
  obtain ⟨h_eq, heven⟩ := h_absurd
  exfalso
  have h1 : ¬ Odd n := by
    exact Nat.not_odd_iff_even.mpr heven
  exact h1 hn