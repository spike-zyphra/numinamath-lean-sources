import Mathlib

theorem algebra_186133 (x y : ℤ) : 2*x^3+x*y-7=0 ↔ (x=-7 ∧ y=-99) ∨ (x=-1 ∧ y=-9) ∨ (x=1 ∧ y=5) ∨ (x=7 ∧ y=-97) := by
  constructor
  · -- Assume 2*x^3 + x*y - 7 = 0, prove the disjunction of the four solutions
    intro h
    have h1 : x ∣ 7 := by
      use 2 * x^2 + y
      linarith
    have h2 : x ≤ 7 := by
      apply Int.le_of_dvd (by norm_num) h1
    have h3 : x ≥ -7 := by
      have h4 : -x ∣ 7 := by 
        exact Int.neg_dvd.2 h1
      have h5 : -x ≤ 7 := by
        apply Int.le_of_dvd (by norm_num) h4
      omega
    interval_cases x <;> try { omega }
    <;> norm_num at h1 h
    <;> try { tauto }
    <;> norm_num at h1 h
    <;> try { tauto }
    <;> norm_num at h1 h
    <;> try { tauto }
    <;> norm_num at h1 h
    <;> try { tauto }
  · -- Assume the disjunction of the four solutions, prove 2*x^3 + x*y - 7 = 0
    rintro (h | h | h | h)
    · -- Case 1: x=-7, y=-99
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case 2: x=-1, y=-9
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case 3: x=1, y=5
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case 4: x=7, y=-97
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num