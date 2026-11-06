import Mathlib

theorem number_theory_301388 (N : ℕ → ℕ) (hN : ∀ n, N n = n ^ 4) :
    ∀ a ∈ Finset.Icc 1 9, N a % 10 = 1 ↔ a = 1 ∨ a = 3 ∨ a = 7 ∨ a = 9 := by
  intro a ha
  have h1 : a ∈ Finset.Icc 1 9 := ha
  rw [Finset.mem_Icc] at h1
  rcases h1 with ⟨ha1, ha2⟩
  have hNa : N a = a ^ 4 := hN a 
  rw [hNa] 
  interval_cases a <;> norm_num at *
  <;> omega