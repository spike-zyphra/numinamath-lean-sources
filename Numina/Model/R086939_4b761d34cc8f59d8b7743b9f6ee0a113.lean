import Mathlib

def is_factorion (n : ℕ) : Prop :=
  n ∈ Finset.Icc 100 999 ∧ n = (Nat.factorial (n / 100)) + (Nat.factorial ((n / 10) % 10)) + (Nat.factorial (n % 10))

theorem number_theory_77400 :
    {n | is_factorion n} = {145} := by
  ext n
  simp [is_factorion, Finset.mem_Icc]
  constructor
  · -- Assume n is a factorion, show n = 145
    intro h
    rcases h with ⟨⟨h100, h999⟩, hfactorion⟩
    interval_cases n <;> norm_num [Nat.factorial] at hfactorion ⊢
    <;> omega
  · -- Assume n = 145, show is a factorion
    intro h
    rw [h]
    constructor
    · -- Show 145 is in range [100, 999]
      norm_num
    · -- Show 145 = 1! + 4! + 5!
      norm_num [Nat.factorial]