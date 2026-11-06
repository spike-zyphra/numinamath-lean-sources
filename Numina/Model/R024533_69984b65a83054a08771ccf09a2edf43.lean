import Mathlib

open Finset

theorem number_theory_102256 {g : ℕ → ℕ} (hg : ∀ n, Odd (g n) ∧ g n ∣ n ∧ ∀ m, Odd m → m ∣ n → m ≤ g n) :
    ∑ i ∈ range (2 ^ n), g (i + 1) = (4 ^ n + 2) / 3 := by 
  have h2 : Odd (g 0) := (hg 0).1
  have h30 : g 0  ∣ 0 := (hg 0).2.1
  have h12 : ∀m, Odd m → m ∣ 0 → m ≤ g 0 := (hg 0).2.2
  -- We can pick m as g0+2
  have h43 := h12 (g 0 + 2) (by
    obtain ⟨k, hk⟩ := h2
    use k + 1
    omega 
  ) (by
    simp 
  )
  exfalso 
  have h46 : g 0 + 2 < (g 0 + 2) := by 
    omega
  omega