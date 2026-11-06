import Mathlib

theorem number_theory_204030 {n : ℕ} (hn : n ≥ 10000000000) :
    (Nat.digits 10 n).length = 10 ∧
    (Nat.digits 10 n).toFinset.card = 10 ∧
    (Nat.ofDigits 10 (List.filter (fun d => Even d) (Nat.digits 10 n))) = 97531 ∧
    (Nat.ofDigits 10 (List.filter (fun d => Odd d) (Nat.digits 10 n))) = 02468 ↔
    n = 9024675318 := by
  constructor
  · -- Forward direction: if n satisfies all conditions, then n = 9024675318
    rintro ⟨h1, h2, h3, h4⟩
    have h6 : (Nat.digits 10 n).length > 10 := by
      have h7 : n ≥ 10000000000 := hn
      have h8 : (Nat.log 10 n) ≥ 10 := by
        have h10 : 10 ^ 10 ≤ n := by linarith
        have h11 : Nat.log 10 n ≥ 10 := by
          apply Nat.le_log_of_pow_le (by norm_num) h10
        linarith
      have h9 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
        rw [Nat.digits_len]
        all_goals
        try { omega }
      omega
    omega
  · -- Backward direction: if n = 9024675318, then all conditions hold
    intro h
    rw [h] at hn
    all_goals
    norm_num at hn ⊢
    all_goals
    try tauto