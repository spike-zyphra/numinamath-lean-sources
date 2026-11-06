import Mathlib

theorem algebra_136911 (a : ℤ) (ha : a ≠ 0) (hne : a ≠ 4) :
    ∃ k : ℤ, (a / (a - 4)) + (2 / a) = k ↔ a = 2 ∨ a = -4 := by 
  have h1 : a ≠ 0 := ha
  have h2 : a ≠ 4 := hne
  use if a = 2 ∨ a = -4 then (a / (a - 4) + (2 / a)) else (a / (a - 4) + (2 / a)) + 1
  split_ifs with h
  · 
    simp [h]
    <;> try { 
      rcases h with (r | r)
      all_goals
      rw [r]
      all_goals norm_num [h1, h2]
      all_goals try { 
        native_decide
      }
    }
    all_goals try { 
        norm_num [h1, h2]
        all_goals try { 
          native_decide
        }
    }
  all_goals simp [h]
  all_goals try { 
    norm_num [h1, h2]
  }
  all_goals try { 
    omega
  }
  all_goals try { 
    norm_num [h1, h2]
    all_goals try { 
      native_decide
    }
    all_goals try { 
      omega
    }
  }
  all_goals try { 
    tauto
  }