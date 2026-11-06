import Mathlib

theorem algebra_306954 :
    {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x^3 - y^3 + x^2 * y - x * y^2 = 32}.encard = 1 := by
  have h1 : {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x^3 - y^3 + x^2 * y - x * y^2 = 32} = {(3, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First direction: if (x, y) is in the set, then (x, y) = (3, 1).
      rintro ⟨hx, hy, heq⟩
      have eq1 : x ^ 3 - y ^ 3 + x ^ 2 * y - x * y ^ 2 = (x - y) * (x + y) ^ 2 := by
        ring
      rw [eq1] at heq
      have h2 : (x - y) * (x + y) ^ 2 = 32 := by
        linarith
      have h3 : x - y > 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
      have h4 : (x - y) ∣ 32 := by
        use (x + y) ^ 2
        all_goals linarith
      have h5 : (x - y) ≥ 1 := by
        omega
      have h6 : (x - y) ≤ 32 := by
        exact Int.le_of_dvd (by norm_num) h4
      interval_cases k : (x - y) <;> try { 
        omega 
      } <;> try { 
        all_goals
        have h7 : (x + y) ^ 2 ≤ 32 := by 
          nlinarith 
        have h8 : (x + y) ≤ 5 := by 
          nlinarith [sq_nonneg (x + y)]
        have h9 : (x + y) ≥ 1 := by 
          nlinarith 
        interval_cases n : (x + y) <;> try { 
          omega 
        } <;> norm_num at h2 
        <;> try { 
          tauto 
        }
      }
      <;> norm_num at h2 
      <;> try { 
        all_goals
        omega 
      }
      <;> try { 
        exfalso
        <;> try { 
          nlinarith 
        }
      }
      <;> try { 
        have h32 : x ≤ 32 := by 
          nlinarith 
        have h33 : y ≤ 32 := by 
          nlinarith 
        interval_cases x <;> try { 
          omega 
        }
        <;> interval_cases y <;> norm_num at h2 <;> try { 
          tauto 
        }
        all_goals 
          try { 
            omega 
          } 
        all_goals 
          try { 
            tauto 
          }
      }
    · -- Second direction: if (x, y) = (3, 1), then it's in the set.
      rintro ⟨rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
  rw [h1]
  simp [Set.encard_singleton]
  all_goals try { 
    aesop 
  }
  <;> try { 
    tauto 
  }