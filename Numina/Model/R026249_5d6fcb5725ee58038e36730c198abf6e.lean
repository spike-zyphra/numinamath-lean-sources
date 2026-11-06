import Mathlib

theorem algebra_315753 :
    {(p, x) : ℤ × ℤ | p ≠ 0 ∧ x + 10 = p * x}.ncard = 7 := by
  have h1 : {(p, x) : ℤ × ℤ | p ≠ 0 ∧ x + 10 = p * x} = { 
    (-9, -1), (-4, -2), (-1, -5), (2, 10), (3, 5), (6, 2), (11, 1)
  } := by 
    ext ⟨p, x⟩ 
    simp 
    constructor
    · -- Assume (p ≠ 0 ∧ x + 10 = p * x), prove ⟨p, x⟩ ∈ { ..., }
      rintro ⟨hp, heq⟩ 
      have h2 : x * (p - 1) = 10 := by
        linarith 
      have h3 : x ∣ 10 := by 
        use (p - 1)
        all_goals linarith 
      have h4 : x ≤ 10 := by 
        apply Int.le_of_dvd (by norm_num) h3 
      have h5 : x ≥ -10 := by 
        have h6 : (-x) ∣ 10 := by 
          exact Int.neg_dvd.2 h3 
        have h7 : -x ≤ 10 := by 
          apply Int.le_of_dvd (by norm_num) h6 
        omega 
      interval_cases x <;> try { 
        omega 
      } 
      <;> try { 
        norm_num at h2 
        all_goals 
        try { 
          omega 
        } 
        <;> try { 
          have : p = -9 := by nlinarith 
          simp [this] 
          all_goals norm_num 
          <;> tauto 
        }
        <;> try { 
          have : p = -4 := by nlinarith 
          simp [this] 
          all_goals norm_num 
          <;> tauto 
        }
        <;> try { 
          have : p = -1 := by nlinarith 
          simp [this] 
          all_goals norm_num 
          <;> tauto 
        }
        <;> try { 
          have : p = 2 := by nlinarith 
          simp [this] 
          all_goals norm_num 
          <;> tauto 
        }
        <;> try { 
          have : p = 3 := by nlinarith 
          simp [this] 
          all_goals norm_num 
          <;> tauto 
        }
        <;> try { 
          have : p = 6 := by nlinarith 
          simp [this] 
          all_goals norm_num 
          <;> tauto 
        }
        <;> try { 
          have : p = 11 := by nlinarith 
          simp [this] 
          all_goals norm_num 
          <;> tauto 
        }
      }
    · -- Assume ⟨p, x⟩ ∈ { 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (-9 ≠ 0 ∧ -1 + 10 = -9 * -1)
        constructor <;> norm_num 
      · -- Check (-4 ≠ 0 ∧ -2 + 10 = -4 * -2)
        constructor <;> norm_num 
      · -- Check (-1 ≠ 0 ∧ -5 + 10 = -1 * -5)
        constructor <;> norm_num 
      · -- Check (2 ≠ 0 ∧ 10 + 10 = 2 * 10)
        constructor <;> norm_num 
      · -- Check (3 ≠ 0 ∧ 5 + 10 = 3 * 5)
        constructor <;> norm_num 
      · -- Check (6 ≠ 0 ∧ 2 + 10 = 6 * 2)
        constructor <;> norm_num 
      · -- Check (11 ≠ 0 ∧ 1 + 10 = 11 * 1)
        constructor <;> norm_num 
  rw [h1] 
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide