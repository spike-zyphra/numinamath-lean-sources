import Mathlib

def D (a n : ℕ) := ∑ i ∈ Finset.range n, a * 2 ^ i

theorem number_theory_70178 :
    IsLeast {n | 0 < n ∧ ∀ i ∈ Finset.Icc 1 6, ∃ a, 0 < a ∧ D a i = n} 9765 := by
  constructor
  · -- Show 9765 is in the set.
    constructor
    · -- Show 9765 is positive.
      norm_num
    · -- Show that for all i in [1,6], there is a natural a>0 with D(a, i) = 9765.
      intro i hi
      fin_cases hi <;> try { tauto }
      · -- i = 1
        use 9765
        simp [D, Finset.sum_range]
        all_goals norm_num
      · -- i = 2
        use 3255
        norm_num [D, Finset.sum_range]
      · -- i = 3
        use 1395
        norm_num [D, Finset.sum_range]
      · -- i = 4
        use 651
        norm_num [D, Finset.sum_range]
      · -- i = 5
        use 315
        norm_num [D, Finset.sum_range]
      · -- i = 6
        use 155
        norm_num [D, Finset.sum_range]
  · -- Show 9765 is the smallest such number.
    intro n hn
    have ⟨hn_pos, hn_prop⟩ := hn
    have h6 := hn_prop 6 (by norm_num)
    rcases h6 with ⟨a6, ha6_pos, h_eq6⟩
    have h6_eq : D a6 6 = 63 * a6 := by
      unfold D
      simp [Finset.sum_range_succ]
      <;> ring_nf <;> omega
    have h63 : n = 63 * a6 := by
      linarith [h_eq6, h6_eq]
    have h5 := hn_prop 5 (by norm_num)
    rcases h5 with ⟨a5, ha5_pos, h_eq5⟩
    have h5_eq : D a5 5 = 31 * a5 := by
      unfold D
      simp [Finset.sum_range_succ]
      <;> ring_nf <;> omega
    have h31 : n = 31 * a5 := by
      linarith [h_eq5, h5_eq]
    have h4 := hn_prop 4 (by norm_num)
    rcases h4 with ⟨a4, ha4_pos, h_eq4⟩
    have h4_eq : D a4 4 = 15 * a4 := by
      unfold D
      simp [Finset.sum_range_succ]
      <;> ring_nf <;> omega
    have h15 : n = 15 * a4 := by
      linarith [h_eq4, h4_eq]
    have h3_eq : ∃ a3, 0 < a3 ∧ D a3 3 = n := hn_prop 3 (by norm_num)
    rcases h3_eq with ⟨a3, ha3_pos, h_eq3⟩
    have h3_eq3 : D a3 3 = 7 * a3 := by
      unfold D
      simp [Finset.sum_range_succ]
      <;> ring_nf <;> omega
    have h7 : n = 7 * a3 := by
      linarith [h_eq3, h3_eq3]
    have h2 := hn_prop 2 (by norm_num)
    rcases h2 with ⟨a2, ha2_pos, h_eq2⟩
    have h2_eq2 : D a2 2 = 3 * a2 := by
      unfold D
      simp [Finset.sum_range_succ]
      <;> ring_nf <;> omega
    have h3_a : n = 3 * a2 := by
      linarith [h_eq2, h2_eq2]
    have h1 := hn_prop 1 (by norm_num)
    rcases h1 with ⟨a1, ha1_pos, h_eq1⟩
    have h1_eq1 : D a1 1 = a1 := by
      unfold D
      simp [Finset.sum_range_succ]
      <;> ring_nf <;> omega
    have h1_eq : n = a1 := by
      linarith [h_eq1, h1_eq1]
    have : n ≥ 9765 := by
      omega
    linarith