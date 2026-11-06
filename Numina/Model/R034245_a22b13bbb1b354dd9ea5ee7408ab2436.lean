import Mathlib

theorem number_theory_164659 : ¬ ∃ n : ℕ, n^2 = ∑ i ∈ Finset.Icc 1991 1996, i^i := by
  rintro ⟨n, hn⟩
  have h1 : n ^ 2 = ∑ i ∈ Finset.Icc 1991 1996, i ^ i := hn 
  have h2 : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by 
    have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1]
  have h3 : (∑ i ∈ Finset.Icc 1991 1996, i ^ i) % 4 = 3 := by 
    native_decide 
  have h4 : (n ^ 2) % 4 = 3 := by 
    omega 
  omega