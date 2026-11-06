import Mathlib

theorem number_theory_198658 :
    ¬∃ n : ℕ, (Nat.digits 10 n).length = 2 ∧
      (Nat.digits 10 n).headI ≠ 0 ∧
      (Nat.digits 10 n).tail.headI ≠ 0 ∧
      n / ((Nat.digits 10 n).headI ^ 2 + (Nat.digits 10 n).tail.headI ^ 2) = 2 ∧
      n % ((Nat.digits 10 n).headI ^ 2 + (Nat.digits 10 n).tail.headI ^ 2) = 6 ∧
      n / ((Nat.digits 10 n).headI * (Nat.digits 10 n).tail.headI) = 4 ∧
      n % ((Nat.digits 10 n).headI * (Nat.digits 10 n).tail.headI) = 6 := by 
  rintro ⟨n, hn1, hn2, hn3, h1, h2, h3, h4⟩
  have h10 : n ≥ 10 := by 
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at *
    <;> norm_num [Nat.digits, Nat.digitsAux] at hn1 hn2 hn3 h1 h2 h3 h4 <;> try { contradiction }
    <;> omega
  have h11 : n ≤ 99 := by 
    by_contra h
    push_neg at h
    have : n ≥ 100 := by omega
    have : (Nat.digits 10 n).length > 2 := by
      have h2 : Nat.log 10 n ≥ 2 := by 
        have : n ≥ 100 := by linarith
        exact Nat.le_log_of_pow_le (by norm_num) this
      have h1 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
        rw [Nat.digits_len]
        all_goals 
          try { linarith }
          <;> try { omega }
          all_goals linarith
      linarith [h1, h2]
    linarith
  interval_cases n <;> norm_num [Nat.digits, Nat.digitsAux] at hn1 hn2 hn3 h1 h2 h3 h4 <;> omega
  all_goals try { contradiction } <;> try { linarith }