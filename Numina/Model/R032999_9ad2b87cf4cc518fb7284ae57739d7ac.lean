import Mathlib

theorem number_theory_98638 (U a : ℤ) (hu₁ : -1000 ≤  U) (hu₂: U ≤ 1000) (ha_pos: 0 < a) (ha: U = ∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n^2 - n * a) / (5:ℝ)⌋) (ha_uniq: ∀ b > 0, U = ∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n^2 - n * a) / (5:ℝ)⌋ → a = b) : a + U = 944 := by 
  have h1 : a = 1 := by
    specialize ha_uniq 1 (by norm_num)
    have h_eq : U = ∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n^2 - n * a) / (5:ℝ)⌋ := by
      linarith [ha]
    have h1 := ha_uniq h_eq
    omega

  have h2 : a = 2 := by
    specialize ha_uniq 2 (by norm_num)
    have h_eq : U = ∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n^2 - n * a) / (5:ℝ)⌋ := by
      linarith [ha]
    have h2 := ha_uniq h_eq
    omega

  omega