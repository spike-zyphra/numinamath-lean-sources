import Mathlib

theorem algebra_21146 : IsLeast {N : ℕ | ∃ a b : ℕ → ℕ, (∀ n, a n ≤ a (n + 1)) ∧ (∀ n, b n ≤ b (n + 1)) ∧ a 0 ≠ b 0 ∧ (∀ n, a (n + 2) = a n + a (n + 1)) ∧ (∀ n, b (n + 2) = b n + b (n + 1)) ∧ N = a 6 ∧ N = b 6} 104 := by
  constructor
  · -- $104$ is such a value, and this is witnessed by $a_0 = 0, a_1 = 13$ and $b_0 = b_2 = 8$
    let a (n : ℕ) : ℕ := ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 13)).fst
    let b (n : ℕ) : ℕ := ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (8, 8)).fst
    use a
    use b
    -- each term of $\{a_n\}$ beginning with the third is the sum of the previous two terms
    have aaddtwo {n : ℕ} : a (n + 2) = a n + a (n + 1) := by
      simp only [Function.iterate_succ_apply', a]
    -- each term of $\{b_n\}$ beginning with the third is the sum of the previous two terms
    have baddtwo {n : ℕ} : b (n + 2) = b n + b (n + 1) := by
      simp only [Function.iterate_succ_apply', b]
    -- $\{a_n\}$ is non-decreasing
    have aleasucc {n : ℕ} : a n ≤ a (n + 1) := by
      cases n <;> simp [aaddtwo]
      exact Nat.le_of_ble_eq_true rfl
    -- $\{b_n\}$ is non-decreasing
    have blebsucc {n : ℕ} : b n ≤ b (n + 1) := by
      cases n <;> simp [baddtwo]
      exact Nat.le_of_ble_eq_true rfl
    -- $a_0 \neq b_0$
    have aneb : a 0 ≠ b 0 := by
      exact Nat.ne_of_beq_eq_false rfl
    -- $N = a_6 = b_6$
    have Neqa : 104 = a 6 := by
      exact rfl
    have Neqb : 104 = b 6 := by
      exact rfl
    exact ⟨(by exact fun n => aleasucc), (by exact fun n => blebsucc), aneb, (by exact fun n => aaddtwo), (by exact fun n => baddtwo), Neqa, Neqb⟩
  · -- $104$ is the least such value
    rintro N ⟨a, b, hamono, hbmono, aneb, hafib, hbfib, Neqa, Neqb⟩
    have ha1 := hafib 0
    have ha2 := hafib 1
    have ha3 := hafib 2
    have ha4 := hafib 3
    have ha5 := hafib 4
    have ha6 := hafib 5
    have hb1 := hbfib 0
    have hb2 := hbfib 1
    have hb3 := hbfib 2
    have hb4 := hbfib 3
    have hb5 := hbfib 4
    have hb6 := hbfib 5
    simp only [hafib, zero_add, Nat.reduceAdd] at Neqa
    ring_nf at Neqa
    simp only [hbfib, zero_add, Nat.reduceAdd] at Neqb
    ring_nf at Neqb
    have ha01 : a 0 ≤ a 1 := by
      apply hamono 0
    have hb01 : b 0 ≤ b 1 := by
      apply hbmono 0
    omega