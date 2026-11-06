import Mathlib

theorem number_theory_223828 (n : ℤ) : ¬ ∃ m, m^2 = ∑ i ∈ Finset.range 7, (n + i)^2 := by 
  rintro ⟨m, hm⟩
  have hm_eq : m ^ 2 % 7 = 0 := by
    have h_eq : m ^ 2 = ∑ i ∈ Finset.range 7, (n + i) ^ 2 := hm
    simp [Finset.sum_range_succ] at h_eq 
    have h2 : m ^ 2 = 7 * (n ^ 2 + 6 * n + 13) := by
      nlinarith
    have h3 : m ^ 2 % 7 = 0 := by
      omega
    assumption

  have h3 : m % 7 = 0 := by
    have h4 : m ^ 2 % 7 = 0 := hm_eq
    have h4 : m % 7 = 0 := by
      have h2 : m % 7 = 0 ∨ m % 7 = 1 ∨ m % 7 = 2 ∨ m % 7 = 3 ∨ m % 7 = 4 ∨ m % 7 = 5 ∨ m % 7 = 6 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2] at h4 ⊢
      all_goals
        omega
    assumption

  have h4 : ∃ k : ℤ, m = 7 * k := by 
    refine' ⟨m / 7, by omega⟩

  rcases h4 with ⟨k, hk⟩
  have eq2 : n ^ 2 + 6 * n + 13 = 7 * k ^ 2 := by
    rw [show m = 7 * k by linarith [hk]] at hm
    norm_num [Finset.sum_range_succ] at hm ⊢
    nlinarith
  -- Now we compute n % 7 from equation `eq2`
  have h5 : (n ^ 2 + 6 * n + 13) % 7 = 0 := by
    omega
  -- Checking all residues to show contradiction
  have h6 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by 
    omega
  rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h6] at h5
  all_goals
    omega