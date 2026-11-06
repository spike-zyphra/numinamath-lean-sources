import Mathlib

open Polynomial

theorem algebra_10220 : ∏ᶠ (t : ℤ) (ht : ∃ a b : ℤ, X ^ 2 + C t * X - 10 = (X + C a) * (X + C b)), t = 729 := by
  have h1 : {t : ℤ | ∃ a b : ℤ, X ^ 2 + C t * X - 10 = (X + C a) * (X + C b)} = {-9, 9, -3, 3} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume that there exists a and b such that X ^ 2 + C t * X - 10 = (X + C a) * (X + C b)
      rintro ⟨a, b, heq⟩
      have eq1 := congr_arg (fun f => f.eval 0) heq
      simp [ eval_add, eval_mul, eval_pow, eval_C] at eq1 
      have eq2 := congr_arg (fun f => f.eval 1) heq 
      simp [ eval_add, eval_mul, eval_pow, eval_C] at eq2 
      have h2 : a * b = -10 := by 
        nlinarith 
      have h3 : a + b = t := by 
        nlinarith 
      have h4 : a * b = -10 := h2 
      have h5 : a ∣ -10 := by
        use b
        all_goals linarith 
      have h6 : a ∣ 10 := by
        exact Int.dvd_neg.mp h5 
      have h7 : a ≤ 10 := by
        apply Int.le_of_dvd (show (0 : ℤ) < 10 by norm_num) h6 
      have h8 : a ≥ -10 := by
        have h9 : (-a) ∣ 10 := by
          exact Int.neg_dvd.2 h6 
        have h10 : -a ≤ 10 := by
          apply Int.le_of_dvd (show (0 : ℤ) < 10 by norm_num) h9 
        omega 
      interval_cases a <;> omega 
    · -- Show that for t in `{ -9, 9, -3, 3 }`, there exists `a, b` satisfying the condition
      rintro (rfl | rfl | rfl | rfl)
      · -- t = -9
        use 1, -10 
        all_goals 
          simp [pow_two]
          <;> ring 
      · -- t = 9 
        use -1, 10 
        all_goals 
          simp [pow_two]
          <;> ring 
      · -- t = -3 
        use 2, -5 
        all_goals 
          simp [pow_two]
          <;> ring 
      · -- t = 3 
        use -2, 5 
        all_goals 
          simp [pow_two]
          <;> ring 
  rw [show ∏ᶠ (t : ℤ) (ht : ∃ a b : ℤ, X ^ 2 + C t * X - 10 = (X + C a) * (X + C b)), t = ∏ᶠ (t : ℤ) (ht : t ∈ {t : ℤ | ∃ a b : ℤ, X ^ 2 + C t * X - 10 = (X + C a) * (X + C b)}), t by 
      congr
    ]
  rw [h1]
  rw [finprod_mem_insert, finprod_mem_insert, finprod_mem_insert, finprod_mem_singleton]
  all_goals norm_num