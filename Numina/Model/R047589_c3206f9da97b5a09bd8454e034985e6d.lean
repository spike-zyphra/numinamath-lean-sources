import Mathlib

theorem algebra_189380 : {(x, y) : ℤ × ℤ | 2*x^2+x*y-y^2=14}.ncard = 8 := by
  have h1 : {(x, y) : ℤ × ℤ | 2*x^2+x*y-y^2=14} = {(-5, 4), (-5, -9), (-3, 1), (-3, -4), (3, 4), (3, -1), (5, -4), (5, 9)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h : 2 * x ^2 + x*y - y^2 = 14, prove (x,y) ∈ right side
      rintro H
      have h_eq : (2 * x - y) * (x + y) = 14 := by
        nlinarith
      have h2 : (2 * x - y) ∣ 14 := by
        use (x + y)
        all_goals nlinarith
      have h3 : (2 * x - y) ≤ 14 := by
        apply Int.le_of_dvd (by norm_num) h2
      have h4 : (2 * x - y) ≥ -14 := by
        have h5 : (- (2 * x - y)) ∣ 14 := by
          exact Int.neg_dvd.2 h2
        have h6 : - (2 * x - y) ≤ 14 := by
          apply Int.le_of_dvd (by norm_num) h5
        omega
      interval_cases h5 : 2 * x - y <;> omega
    · -- Show that if (x,y) ∈ right side, then 2*x^2 + x*y - y^2 = 14
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (-5, 4)
        norm_num
      · -- (-5, -9)
        norm_num
      · -- (-3, 1)
        norm_num
      · -- (-3, -4)
        norm_num
      · -- (3, 4)
        norm_num
      · -- (3, -1)
        norm_num
      · -- (5, -4)
        norm_num
      · -- (5, 9)
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }