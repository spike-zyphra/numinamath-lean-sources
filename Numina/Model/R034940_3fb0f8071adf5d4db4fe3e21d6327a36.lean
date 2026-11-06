import Mathlib

theorem number_theory_11895 {S : ℕ → ℕ} (hS₁: S 1 = 7) (hSₙ : ∀ n > 1, S n = 7 ^ (S (n - 1))) : S 100 ≡ 3 [MOD 5] := by 
  have h1 : ∀ (n : ℕ), n > 1 → S n % 4 = 3 := by
    intro n hn
    induction n with
    | zero => linarith
    | succ n ih => 
      cases n with
      | zero => linarith
      | succ n => 
        cases n with
        | zero => 
          simp [Nat.ModEq, hSₙ, hS₁]
          <;> norm_num
        | succ n => 
          have h2 : (n + 2 + 1) = (n + 3) := by ring_nf
          rw [h2]
          have h2' : S (n + 3) = 7 ^ (S (n + 2)) := by
            specialize hSₙ (n + 3) (by omega)
            simpa using hSₙ
          rw [h2']
          have h4 : S (n + 2) % 4 = 3 := by
            apply ih
            all_goals omega
          have h5 : ∃ k, S (n + 2) = 4 * k + 3 := by
            refine' ⟨(S (n + 2) - 3) / 4, by omega⟩
          rcases h5 with ⟨k, hk⟩
          have h6 : (7 ^ (S (n + 2)) ) % 4 = 3 := by
            rw [hk]
            have h8 : ∀ (k : ℕ), (7 : ℕ) ^ (4 * k + 3) % 4 = 3 := by
              intro k
              induction k with
              | zero => 
                norm_num
              | succ k ih => 
                ring_nf at ih ⊢
                all_goals omega
            exact h8 k
          exact h6
    <;> try { omega }
    <;> try { tauto }
    <;> try { tauto }
    <;> try { omega }
  have h2 : S 99 % 4 = 3 := h1 99 (by norm_num)
  rw [hSₙ 100 (by norm_num)]
  have h3 : (7 ^ (S 99) ) % 5 = 3 := by
    have h4 : S 99 % 4 = 3 := h2
    have h5 : ∃ k, S 99 = 4 * k + 3 := by
      refine' ⟨(S 99 - 3) / 4, by omega⟩
    rcases h5 with ⟨k, hk⟩
    have h6 : (7 ^ (S 99) ) % 5 = 3 := by
      rw [hk]
      have h8 : ∀ (k : ℕ), (7 : ℕ) ^ (4 * k + 3) % 5 = 3 := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih => 
          ring_nf at ih ⊢
          all_goals omega
      exact h8 k
    exact h6
  simp [Nat.ModEq, h3]
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { try { tauto } <;> try { omega } }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }