import Mathlib

theorem number_theory_39125 (a : ℕ → ℤ)
    (h₀ : ∀ n, ∑ i in Finset.range n, a i = (n ^ 2) * n) :
    a 2020 % 1000 = 261 := by
  have eq1 : a 2020 = (∑ i in Finset.range 2021, a i) - (∑ i in Finset.range 2020, a i) := by 
    have eq2 : (∑ i in Finset.range 2021, a i) = (∑ i in Finset.range 2020, a i) + a 2020 := by
      rw [Finset.sum_range_succ]
      <;> try simp
    linarith
  have eq2 : (∑ i in Finset.range 2021, a i) = (2021 : ℤ) ^ 3 := by 
    specialize h₀ 2021
    norm_num at h₀ ⊢
    all_goals linarith
  have eq3 : (∑ i in Finset.range 2020, a i) = (2020 : ℤ) ^ 3 := by 
    specialize h₀ 2020
    norm_num at h₀ ⊢
    all_goals linarith
  have eq4 : a 2020 = (2021 : ℤ) ^ 3 - (2020 : ℤ) ^ 3 := by 
    rw [eq2, eq3] at eq1
    linarith
  rw [eq4]
  norm_num