import Mathlib

theorem algebra_269115 (n : ℤ) :
    ∃ m, m^2 = n^2 + 6 * n + 24 ↔ n = 4 ∨ n = -2 ∨ n = -4 ∨ n = -10 := by 
  by_cases h1 : n = 4
  · -- Assume n = 4, so m^2 = 64, so m = 8 or m = -8. Let's pick 8.
    use 8
    simp [h1]
    <;> norm_num 
    <;> tauto
  by_cases h2 : n = -2
  · -- Assume n = -2, so m = 4. This works.
    use 4
    simp [h2]
    <;> norm_num 
    <;> tauto
  by_cases h3 : n = -4
  · -- Assume n = -4, so m = 4. This works.
    use 4
    simp [h3]
    <;> norm_num 
    <;> tauto
  by_cases h4 : n = -10
  · -- Assume n = -10, so m = 8. This works.
    use 8
    simp [h4]
    <;> norm_num 
    <;> tauto
  · -- Assume n is none of {4, -2, -4, -10}, then the quadratic can't be a square.
    use 0
    simp at *
    all_goals 
      try { 
        have h5 : n^2 + 6 * n + 24 > 0 := by nlinarith [sq_nonneg (n + 3)]
        try { 
          omega 
        }
        <;> try { 
          nlinarith [sq_nonneg (n + 3)]
        }
      }
      <;> try { 
        omega 
      }
      <;> try { 
        nlinarith [sq_nonneg (n + 3)]
      }
      <;> try { 
        omega 
      }
      <;> try { 
        nlinarith [sq_nonneg (n + 3)]
      }
      all_goals try { 
        omega 
      }
      all_goals try { 
        nlinarith [sq_nonneg (n + 3)]
      }
      all_goals try { 
        omega 
      }
      all_goals try { 
        nlinarith [sq_nonneg (n + 3)]
      }
      all_goals try { 
        nlinarith [sq_nonneg (n + 3)]
      }
      all_goals try { 
        omega 
      }