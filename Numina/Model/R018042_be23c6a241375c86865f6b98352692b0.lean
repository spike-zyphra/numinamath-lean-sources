import Mathlib

theorem algebra_168059 {a b c : ℕ → ℤ} (ha1 : a 1 = 1) (hb1 : b 1 = 3) (hc1 : c 1 = 2)
    (hinc : ∀ i ≥ 1, a (i + 1) = a i + c i - b i + 2 ∧ b (i + 1) = (3 * c i - a i + 5) / 2 ∧ c (i + 1) = 2 * a i + 2 * b i - 3) :
    ∀ n ≥ 1, a n = 2 ^ (n - 1) ∧ b n = 2 ^ n + 1 ∧ c n = 3 * 2 ^ (n - 1) - 1 := by
  intro n hn
  induction n with
  | zero =>
    exfalso 
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      constructor 
      · exact ha1
      constructor 
      · exact hb1 
      · exact hc1
    | succ n =>
      have h2 := hinc (n + 1) (by linarith)
      rcases h2 with ⟨ha2, hb2, hc2⟩
      rcases ih (by linarith) with ⟨ha, hb, hc⟩
      constructor
      · -- Prove a (n + 2) = 2 ^ ((n + 2) - 1)
        rw [ha2]
        simp [ha, hb, hc] at *
        <;> cases n with
        | zero =>
          all_goals
            norm_num
        | succ n =>
          all_goals 
            ring_nf <;> omega 
      constructor
      · -- Prove b (n + 2) = 2 ^ (n + 2) + 1
        rw [hb2]
        simp [ha, hb, hc] at *
        <;> cases n with
        | zero =>
          all_goals
            norm_num 
        | succ n =>
          all_goals 
            ring_nf <;> omega 
      · -- Prove c (n + 2) = 3 * 2 ^ ((n + 2) - 1) - 1
        rw [hc2]
        simp [ha, hb, hc] at *
        <;> cases n with
        | zero =>
          all_goals
            norm_num 
        | succ n =>
          all_goals 
            ring_nf <;> omega