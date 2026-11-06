import Mathlib

theorem number_theory_128812 :
    Set.ncard {n : ℤ | n ∈ Finset.Icc (-30) 100 ∧ 5 ∣ n^3 + 4 * n^2 + n - 6} = 78 ∧
    IsGreatest {n | n ∈ Finset.Icc (-30) 100 ∧ 5 ∣ n^3 + 4 * n^2 + n - 6} 98 ∧
    IsLeast {n | n ∈ Finset.Icc (-30) 100 ∧ 5 ∣ n^3 + 4 * n^2 + n - 6} (-29) := by
  have h1 : {n : ℤ | n ∈ Finset.Icc (-30) 100 ∧ 5 ∣ n^3 + 4 * n^2 + n - 6} = Finset.filter (fun n => 5 ∣ n^3 + 4 * n^2 + n - 6) (Finset.Icc (-30) 100) := by
    ext n
    simp
  rw [h1] at *
  constructor
  · -- Show that the cardinality of the set is 78
    rw [Set.ncard_coe_Finset]
    native_decide
  constructor
  · -- Show that 98 is greatest
    constructor
    · -- Show 98 is in the set
      native_decide
    · -- Show that for all n in the set, n ≤ 98
      intro n hn
      simp [Finset.mem_Icc] at hn
      by_contra h
      push_neg at h
      have h2 : n ≤ 100 := by linarith
      have h3 : n > 98 := by linarith
      have h4 : n ≤ 100 := by linarith
      interval_cases n <;> norm_num at hn ⊢ <;> omega
  · -- Show that -29 is least
    constructor
    · -- Show -29 is in the set
      native_decide
    · -- Show that for all n in the set, -29 ≤ n
      intro n hn
      simp [Finset.mem_Icc] at hn
      by_contra h
      push_neg at h
      have h1 : n < -29 := by linarith
      have h2 : n ≥ -30 := by linarith
      have h3 : n < -29 := by linarith
      interval_cases n <;> norm_num at hn ⊢ <;> omega