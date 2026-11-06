import Mathlib

theorem number_theory_15375 {n : ℕ} (hn : n % 8 = 6 ∧ n % 9 = 6):
    n ∈ Finset.Ioo 100 200 ↔ n = 150 := by
  constructor
  · -- Assume n ∈ (100,200) and n%8=6 and n%9=6 prove n=150
    intro h
    rw [Finset.mem_Ioo] at h
    rcases hn with ⟨h8, h9⟩
    omega
  · -- Assume n=150 prove n ∈ (100,200)
    intro h
    rw [h]
    exact Finset.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩