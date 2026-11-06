import Mathlib

theorem number_theory_92964 {N : ℕ} (hN : N ∈ Finset.Icc 10 99) (h1 : N ≡ 1 [MOD 9]) (h2 : N ≡ 3 [MOD 10]) :
N % 11 = 7 := by
  rw [Finset.mem_Icc] at hN
  rcases hN with ⟨h3, h4⟩
  norm_num [Nat.ModEq] at h1 h2
  interval_cases N <;> omega