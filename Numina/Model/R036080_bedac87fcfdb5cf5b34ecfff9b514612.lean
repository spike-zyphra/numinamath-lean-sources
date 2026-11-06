import Mathlib

theorem number_theory_207885 {n m : ℕ} (hn : n > 1) (hm : m > 1)
    (h : Nat.digits n 101 = [1, 0, 1]) (h' : Nat.digits m 11011 = [1, 0, 1]) :
    n = 184 ∧ m = 184 := by
  have eq1 : n^2 = 100 := by
    have h1 : Nat.ofDigits n (Nat.digits n 101) = 101 := by
      rw [Nat.ofDigits_digits]
      all_goals linarith
    rw [h] at h1
    simp [Nat.ofDigits, List.foldl] at h1 
    nlinarith
  have hn10 : n = 10 := by
    nlinarith
  have eq2 : m^2 = 11010 := by
    have h2 : Nat.ofDigits m (Nat.digits m 11011) = 11011 := by
      rw [Nat.ofDigits_digits]
      all_goals linarith
    rw [h'] at h2
    simp [Nat.ofDigits, List.foldl] at h2 
    nlinarith
  have h3 : m ≤ 105 := by
    nlinarith
  interval_cases m <;> try { omega } <;> try { norm_num at eq2 <;> all_goals try { tauto } }
  all_goals omega