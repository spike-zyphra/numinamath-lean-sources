import Mathlib

theorem algebra_179234 :
    Set.ncard {n : ℕ | ∃ a : ℤ, ∑ i ∈ Finset.range n, (a + 2 * i) = 153 ∧ n > 1} = 5 := by
  have h1 : {n : ℕ | ∃ a : ℤ, ∑ i in Finset.range n, (a + 2 * i) = 153 ∧ n > 1} = {3, 9, 17, 51, 153} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First direction: existence implies membership in {3, 9, 17, 51, 153}
      rintro ⟨a, hn, hn2⟩
      have h2 : n ≥ 2 := by
        omega
      have h3 : ∀ (n : ℕ), ∑ i in Finset.range n, (a + 2 * (i : ℤ)) = (n : ℤ) * (a + (n : ℤ) - 1) := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          simp [add_mul, mul_add]
          <;> ring
      have h4 : (n : ℤ) * (a + (n : ℤ) - 1) = 153 := by
        rw [h3 n] at hn
        all_goals
          linarith
      have h5 : (n : ℤ) ∣ 153 := by
        use a + (n : ℤ) - 1
        all_goals
          linarith
      have h6 : n ∣ 153 := by
        exact Int.ofNat_dvd.mp h5
      have h7 : n ≤ 153 := by
        exact Nat.le_of_dvd (by norm_num) h6
      interval_cases n <;> norm_num at h6 h4 <;> omega
    · -- Second direction: membership in {3, 9, 17, 51, 153} implies existence
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- n = 3
        use 49
        norm_num [Finset.sum_range_succ]
      · -- n = 9
        use 9
        norm_num [Finset.sum_range_succ]
      · -- n = 17
        use -7
        norm_num [Finset.sum_range_succ]
      · -- n = 51
        use -47
        norm_num [Finset.sum_range_succ]
      · -- n = 153
        use -151
        norm_num [Finset.sum_range_succ]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }