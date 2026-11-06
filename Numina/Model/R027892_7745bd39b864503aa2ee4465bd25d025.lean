import Mathlib

theorem algebra_305202 (f : ℤ → ℤ) (hf : f = fun x => x^2 + 5 * x - 20) :
    {x | ∃ n, n^2 = f x} = {3, 4, 7, 24, -8, -9, -12, -29} := by

  ext x
  simp only [hf, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]

  constructor 
  · -- If there exists an integer n such that n^2 = x^2 + 5 * x - 20, then x must be one of the eight values.
    intro h 
    rcases h with ⟨n, hn⟩
    have h1 : (2 * x + 5 - 2 * n) * (2 * x + 5 + 2 * n) = 105 := by
      nlinarith
    have h2 : (2 * x + 5 - 2 * n) ∣ 105 := by 
      use (2 * x + 5 + 2 * n)
      all_goals nlinarith
    have h3 : (2 * x + 5 - 2 * n) ≤ 105 := by 
      apply Int.le_of_dvd (by norm_num) h2
    have h4 : (2 * x + 5 - 2 * n) ≥ -105 := by 
      have h5 : (- (2 * x + 5 - 2 * n)) ∣ 105 := by 
        exact Int.neg_dvd.2 h2
      have h6 : - (2 * x + 5 - 2 * n) ≤ 105 := by 
        apply Int.le_of_dvd (by norm_num) h5
      omega
    interval_cases h5 : 2 * x + 5 - 2 * n <;> omega

  · -- Assume x is in the set {3, 4, 7, 24, -8, -9, -12, -29}, then there exists integer n such that n^2 = f x.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- x=3
      use 2
      all_goals norm_num
    · -- x=4
      use 4
      all_goals norm_num
    · -- x=7
      use 8
      all_goals norm_num
    · -- x=24
      use 26
      all_goals norm_num
    · -- x=-8
      use 2
      all_goals norm_num
    · -- x=-9
      use 4
      all_goals norm_num
    · -- x=-12
      use 8
      all_goals norm_num
    · -- x=-29
      use 26
      all_goals norm_num