import Mathlib


theorem number_theory_124798 (n : ℕ) (h₀ : n ∈ Finset.Icc 1 2021) (h₁ : ∑ i ∈ Finset.Icc 1 2021 \ {n}, i ≡ 0 [ZMOD 2022]) :
    n = 1011 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨hn1, hn2⟩
  norm_num [Int.ModEq] at h₁
  have h2 : (n : ℤ) ≥ 1 := by omega
  have h3 : (n : ℤ) ≤ 2021 := by omega
  have h4 : ∑ i in (Finset.Icc 1 2021 \ {n} : Finset ℕ), (i : ℤ) = ∑ i in (Finset.Icc 1 2021 : Finset ℕ), (i : ℤ) - (n : ℤ) := by
    have h5 : n ∈ (Finset.Icc 1 2021 : Finset ℕ) := by
      simp at *
      all_goals omega
    rw [Finset.sum_eq_add_sum_diff_singleton h5]
    all_goals
      simp at *
      all_goals omega
  rw [h4] at h₁
  have h5 : (∑ i in (Finset.Icc 1 2021 : Finset ℕ), (i : ℤ)) % 2022 = 1011 := by
    native_decide
  omega