import Mathlib

theorem number_theory_73434 (x : ℕ → ℕ)
    (hx1 : x 1 = 1)
    (hxn : ∀ n, 1 ≤ n → x (n + 1) = 1 + ∑ i in Finset.Icc 1 n, (x i) ^ 2) :
    ∀ m, ∃ n, 1 ≤ n ∧ x n = m ^ 2 → m = 1 := by 
  intro m 
  use 1
  intro h
  have h1 : x 1 = 1 := hx1
  have h2 : x 1 = m ^ 2 := h.2
  rw [h1] at h2
  nlinarith