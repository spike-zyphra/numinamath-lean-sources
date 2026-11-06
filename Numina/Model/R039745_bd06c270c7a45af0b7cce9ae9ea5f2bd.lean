import Mathlib



lemma lemma_1 (x y : ℤ) (h : 7 * x + 6 * y = 2 * x * y) :
    (2 * x - 6) * (2 * y - 7) = 42 := by
  nlinarith


theorem algebra_13446 :
    {(x, y) : ℤ × ℤ | 7 * x + 6 * y = 2 * x * y}.ncard = 8 := by
  have h1 : {(x, y) : ℤ × ℤ | 7 * x + 6 * y = 2 * x * y} = {
      (4, 14), (6, 7), (10, 5), (24, 4), (2, -7), (0, 0), (-18, 3), (-4, 2)
    } := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume that x and y solve 7x + 6y = 2xy, prove they are in our set
      intro h
      have h2 : (2 * x - 6) * (2 * y - 7) = 42 := by
        nlinarith
      have h3 : (2 * x - 6) ∣ 42 := by
        use (2 * y - 7)
        all_goals nlinarith
      have h4 : (2 * x - 6) ∣ 42 := h3
      have h5 : (2 * x - 6) ≤ 42 := by
        apply Int.le_of_dvd (show (0 : ℤ) < 42 by norm_num) h3
      have h6 : (2 * x - 6) ≥ -42 := by
        have h7 : -(2 * x - 6) ∣ 42 := by
          exact Int.neg_dvd.2 h3
        have h8 : -(2 * x - 6) ≤ 42 := by
          apply Int.le_of_dvd (show (0 : ℤ) < 42 by norm_num) h7
        omega
      interval_cases k : (2 * x - 6) <;> omega
    · -- Assume that x and y are in our set, prove they solve 7x + 6y = 2xy
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | 
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }