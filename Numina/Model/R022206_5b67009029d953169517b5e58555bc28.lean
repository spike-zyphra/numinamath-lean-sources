import Mathlib

theorem algebra_53563 {p : ℕ} (hp : Nat.Prime p) (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : p * (x - 2) = x * (y - 1)) (h2 : x + y = 21) :
    (x, y, p) = (11, 10, 11) ∨ (x, y, p) = (14, 7, 7) := by 
  have h4 : y = 21 - x := by
    omega 
  rw [h4] at h1 
  have h5 : x ≤ 21 := by 
    omega 
  have h6 : x ≤ 20 := by
    omega
  interval_cases x <;> norm_num [Prod.ext_iff] at h1 h2 ⊢
  all_goals
    try { 
      have h7 : p ≤ 100 := by 
        nlinarith
      interval_cases p <;> norm_num at hp h1 h2 ⊢ 
    }
  all_goals 
    try { 
      try { 
        tauto 
      }
      all_goals 
        try { 
          contradiction 
        }
      all_goals 
        try { 
          omega 
        }
      all_goals 
        try { 
          trivial 
        }
    }