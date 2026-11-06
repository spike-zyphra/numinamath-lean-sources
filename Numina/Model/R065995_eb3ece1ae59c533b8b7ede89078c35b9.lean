import Mathlib

theorem number_theory_212929 (n : ℕ) :
    n > 0 ∧ n < 1000 ∧ (Nat.digits 10 n).sum^3 = n^2 ↔ n = 1 ∨ n = 27 := by 
        constructor
        · -- Assume n > 0 ∧ n < 1000 ∧ (Nat.digits 10 n).sum^3 = n^2, prove n = 1 ∨ n = 27
            rintro ⟨hn1, hn2, h⟩
            interval_cases n <;> norm_num at h ⊢ <;> omega
        · -- Assume n = 1 ∨ n = 27, prove n > 0 ∧ n < 1000 ∧ (Nat.digits 10 n).sum^3 = n^2
            rintro (rfl | rfl)
            · -- Case n = 1
                constructor
                · norm_num 
                constructor
                · norm_num
                · -- Show that (Nat.digits 10 1).sum^3 = 1^2
                  norm_num
            · -- Case n = 27
                constructor
                · norm_num
                constructor
                · norm_num
                · -- Show that (Nat.digits 10 27).sum^3 = 27^2
                  norm_num