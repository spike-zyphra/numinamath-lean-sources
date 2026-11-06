import Mathlib

theorem number_theory_181286 (n : ℕ) (h : n ∈ Finset.Icc 100 999) (h' : 7 * n ≡ 638 [MOD 1000]) :
    n = 234 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨h1, h2⟩
  norm_num [Nat.ModEq] at h'
  omega