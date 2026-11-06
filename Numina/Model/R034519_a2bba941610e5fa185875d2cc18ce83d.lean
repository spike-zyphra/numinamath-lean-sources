import Mathlib

theorem number_theory_236152 :
    IsGreatest {n | n ≥ 10000 ∧ Nat.digits 10 n = [a, b, c, d, e] ∧ a = e ∧ b = d ∧ c = c ∧ 45 ∣ n} 9999 ∧
    IsLeast {n | n ≥ 10000 ∧ Nat.digits 10 n = [a, b, c, d, e] ∧ a = e ∧ b = d ∧ c = c ∧ 45 ∣ n} 10005 →
    9999 - 10005 = 9090 := by
  intro h
  rcases h with ⟨hg, hl⟩
  norm_num [IsGreatest] at hg
  all_goals 
    norm_num [IsLeast] at hl 
    all_goals 
      omega