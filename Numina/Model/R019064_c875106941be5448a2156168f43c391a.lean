import Mathlib

theorem number_theory_175009 (n : ℕ) :
    ∃ k, k ∈ Finset.Icc n (n + 4) ∧ 3 ∣ k ∧ {x | x ∈ Finset.Icc n (n + 4) ∧ 3 ∣ x}.encard ≤ 2 := by
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h1 with (h | h | h)
  · -- Case where n % 3 = 0
    use n
    constructor
    · -- Show n is in the interval
      simp [Finset.mem_Icc]
      all_goals omega
    constructor
    · -- Show 3 divides n
      omega
    · -- Show the cardinality is ≤ 2
      have h2 : {x | x ∈ Finset.Icc n (n + 4) ∧ 3 ∣ x} = {n, n + 3} := by
        ext x
        simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · -- Assume x ∈ {y | y ∈ [n, n + 4] ∧ 3 ∣ y}
          intro h
          rcases h with ⟨⟨hx1, hx2⟩, hx3⟩
          have h4 : x % 3 = 0 := by
            omega
          omega
        · -- Assume x is in {n, n + 3}
          rintro (rfl | rfl)
          · -- Case x = n
            constructor
            · -- Show n ∈ [n, n + 4]
              simp [Finset.mem_Icc]
              all_goals omega
            · -- Show 3 divides n
              omega
          · -- Case x = n + 3
            constructor
            · -- Show n + 3 ∈ [n, n + 4]
              simp [Finset.mem_Icc]
              all_goals omega
            · -- Show 3 divides n + 3
              omega
      rw [h2]
      rw [Set.encard_pair]
      all_goals omega
  · -- Case n % 3 = 1
    use n + 2
    constructor
    · -- Show n + 2 is in the interval
      simp [Finset.mem_Icc]
      all_goals omega
    constructor
    · -- Show 3 divides n + 2
      omega
    · -- Show the cardinality is ≤ 2
      have h2 : {x | x ∈ Finset.Icc n (n + 4) ∧ 3 ∣ x} = {n + 2} := by
        ext x
        simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · -- Assume x ∈ {y | y ∈ [n, n + 4] ∧ 3 ∣ y}
          intro h
          rcases h with ⟨⟨hx1, hx2⟩, hx3⟩
          have h4 : x % 3 = 0 := by
            omega
          omega
        · -- Assume x = n + 2
          intro h
          rw [h]
          constructor
          · -- Show n + 2 ∈ [n, n + 4]
            simp [Finset.mem_Icc]
            all_goals omega
          · -- Show 3 divides n + 2
            omega
      rw [h2]
      simp [Set.encard_singleton]
      <;> try { tauto }
  · -- n % 3 = 2
    use n + 1
    constructor
    · -- Show n + 1 is in the interval
      simp [Finset.mem_Icc]
      all_goals omega
    constructor
    · -- Show 3 divides n + 1
      omega
    · -- Show the cardinality is ≤ 2
      have h2 : {x | x ∈ Finset.Icc n (n + 4) ∧ 3 ∣ x} = {n + 1, n + 4} := by
        ext x
        simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
        constructor
        · -- Assume x is in the set
          intro h
          rcases h with ⟨⟨hx1, hx2⟩, hx3⟩
          have hx4 : x % 3 = 0 := by
            omega
          have h5 : x = n + 1 ∨ x = n + 4 := by
            omega
          tauto
        · -- Assume x is in {n + 1, n + 4}
          rintro (rfl | rfl)
          · -- Case x = n + 1
            constructor
            · -- Show n + 1 ∈ [n, n + 4]
              simp [Finset.mem_Icc]
              all_goals omega
            · -- Show 3 divides n + 1
              omega
          · -- Case x = n + 4
            constructor
            · -- Show n + 4 ∈ [n, n + 4]
              simp [Finset.mem_Icc]
              all_goals omega
            · -- Show 3 divides n + 4
              omega
      rw [h2]
      have h3 : (n + 1 : ℕ) ≠ (n + 4 : ℕ) := by
        omega
      rw [Set.encard_pair h3]
      all_goals omega