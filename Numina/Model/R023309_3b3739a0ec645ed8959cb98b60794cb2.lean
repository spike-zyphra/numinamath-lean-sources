import Mathlib

theorem number_theory_15476 {n : ℕ} (hn : n = 2^3 * 3^2 * 5) :
    {x | Even x ∧ x ∣ n}.encard = 18 := by
  rw [hn]
  have h1 : {x | Even x ∧ x ∣ 2^3 * 3^2 * 5} = {2, 4, 6, 8, 10, 12, 18, 20, 24, 30, 36, 40, 60, 72, 90, 120, 180, 360} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is even and divides 2^3 * 3^2 * 5
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h2 : x ∣ 2^3 * 3^2 * 5 := hx2
      have h3 : x ≤ 2^3 * 3^2 * 5 := by 
        exact Nat.le_of_dvd (by norm_num) h2
      interval_cases x <;> norm_num [Nat.even_iff] at hx1 h2 ⊢
      <;> tauto
    · -- Assume x is in the explicit set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 2
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 4
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 6
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 8
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 10
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 12
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 18
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 20
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 24
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 30
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 36
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 40
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 60
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 72
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 90
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 120
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 180
        constructor
        · -- even
          decide
        · -- divides
          norm_num
      · -- x = 360
        constructor
        · -- even
          decide
        · -- divides
          norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }