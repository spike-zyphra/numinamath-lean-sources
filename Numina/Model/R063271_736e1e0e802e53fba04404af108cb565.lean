import Mathlib

def is_sam_azing (n : ℕ) := n = (Nat.digits 10 n).sum * (Nat.digits 10 n).prod

theorem number_theory_8728 {n : ℕ} (hn : n ∈ Finset.Icc 100 999) :
    is_sam_azing n ∧ is_sam_azing (n + 9) ↔ n = 135 := by 
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨h₃, h₄⟩
  constructor
  · -- Assume that both n and n + 9 are Sam-azing numbers, prove n = 135
    intro h
    rcases h with ⟨h₁, h₂⟩
    interval_cases n <;> norm_num [is_sam_azing] at h₁ h₂ <;> omega
  · -- Assume n = 135, prove both n and n + 9 are Sam-azing
    intro h
    rw [h]
    constructor
    · -- Show 135 is Sam-azing
      norm_num [is_sam_azing]
    · -- Show 144 is Sam-azing
      norm_num [is_sam_azing]