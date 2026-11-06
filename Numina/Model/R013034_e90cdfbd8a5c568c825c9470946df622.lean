import Mathlib

theorem algebra_21942 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : p < 10) (h' : q < 100) (h'' : p + q = 100) :
    p * q = 291 := by

  have hp1 : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by 
    interval_cases p <;> norm_num at hp ⊢ <;> tauto
  
  rcases hp1 with (rfl | rfl | rfl | rfl)

  · -- p = 2
    have hq1 : q = 98 := by
      omega
    rw [hq1] at hq
    norm_num at hq

  · -- p = 3 
    have hq1 : q = 97 := by 
      omega
    have : 3 * q = 291 := by
      calc
        3 * q = 3 * 97 := by rw [hq1]
        _ = 291 := by norm_num
    exact_mod_cast this
  
  · -- p = 5
    have hq1 : q = 95 := by
      omega
    rw [hq1] at hq
    norm_num at hq
  
  · -- p = 7
    have hq1 : q = 93 := by 
      omega 
    rw [hq1] at hq 
    norm_num at hq