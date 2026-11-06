import Mathlib

theorem number_theory_600537 (A B : ℕ) (hA : A ≤ 30) (hB : B ≤ 30)
    (hAB : A > 0 ∧ B > 0) (hA' : 5 * A + 0 * (30 - A) > 80)
    (hB' : ¬∃! x, 5 * x + 0 * (30 - x) = 80) :
    5 * A + 0 * (30 - A) = 119 := by 
        exfalso 
        apply hB' 
        use 16 
        simp 
        try { 
          intro y h1 
          omega 
        }
        all_goals try { 
          omega 
        }
        all_goals try { tauto }
        all_goals try { 
          omega 
        }