import Mathlib

theorem my_favorite_theorem :
  IsLeast {n : ℕ | n > 0 ∧ ∀ p, p.Prime → (p - 1) ∣ n → p ∣ n} 1806 := by

  constructor
  . simp
    intro p hp_prime hp_sub1_dvd
    have h_p_le_1807 : p ≤ 1807 := by
      apply Nat.le_of_dvd (by norm_num) at hp_sub1_dvd
      omega
    interval_cases p
    all_goals try omega
    all_goals contrapose hp_prime; try norm_num

  . unfold lowerBounds
    simp
    intro n hn_pos hn
    have hn2 := hn 2 (by norm_num) (by norm_num)
    have hn3 := hn 3 (by norm_num) (by omega)
    have hn7 := hn 7 (by norm_num) (by omega)
    have hn43 := hn 43 (by norm_num) (by omega)
    have : 1806 ∣ n := by omega
    apply Nat.le_of_dvd hn_pos at this
    exact this
