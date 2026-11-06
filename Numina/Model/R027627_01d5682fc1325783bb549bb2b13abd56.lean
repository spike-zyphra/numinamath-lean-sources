import Mathlib

theorem number_theory_271653 {p : ℕ} (hp : Nat.Prime p) (a : ZMod p) (ha : a ≠ 0) :
    (a ^ (p - 1) - 1) = 0 := by
  have h2 : Fact (Nat.Prime p) := ⟨hp⟩
  have h1 : a ^ (p - 1) = 1 := by 
    apply ZMod.pow_card_sub_one_eq_one 
    all_goals 
      try { 
        tauto 
      }
  rw [h1]
  all_goals
    try { 
      norm_num 
    }
  all_goals
    try { 
      tauto 
    }