import Mathlib

open Finset

theorem number_theory_298731 {g : ℕ → ℕ} (hg : ∀ k, Odd (g k) ∧ g k ∣ k ∧ ∀ m, Odd m → m ∣ k → m ≤ g k) :
    ∀ n, ∑ i ∈ range (2 ^ n), g (i + 1) = (4 ^ n + 2) / 3 := by
  have h0 := hg 0
  have h8 := h0.2.2 (g 0 + 2)
  have h9 : Odd (g 0 + 2) := by
    have h6 : Odd (g 0) := h0.1
    have h6 : (g 0) % 2 = 1 := by
      rcases h6 with ⟨k, hk⟩
      omega
    have h9 : (g 0 + 2) % 2 = 1 := by
      omega
    exact ⟨(g 0 + 2) / 2, by omega⟩
  have h10 : (g 0 + 2) ∣ 0 := by
    simp
  have h11 := h8 h9 h10
  have h12 : (g 0 + 2) ≤ g 0 := by
    omega
  have h13 : g 0 < (g 0 + 2) := by
    omega
  linarith