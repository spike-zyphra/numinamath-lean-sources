import Mathlib

/- Two non-decreasing sequences of nonnegative integers have different first terms. Each sequence has the property that each term beginning with the third is the sum of the previous two terms, and the seventh term of each sequence is $N$. What is the smallest possible value of $N$? -/
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
  -- $104$ is the least such value
  intro N Nin
  rcases Nin with ⟨a, b, hamono, hbmono, aneb, hafib, hbfib, Neqa, Neqb⟩
  -- $N = 5a_0 + 8a_1 = 5b_0 + 8b_1$
  simp only [hafib, zero_add, Nat.reduceAdd] at Neqa
  ring_nf at Neqa
  simp only [hbfib, zero_add, Nat.reduceAdd] at Neqb
  ring_nf at Neqb
  -- without loss of generality, assume that $a_0 < b_0$
  have Nge (a0 b0 a1 b1 : ℕ) : a0 < b0 → b0 ≤ b1 → N = a0 * 5 + a1 * 8 → N = b0 * 5 + b1 * 8 → 104 ≤ N := by
    intro altb b0le Neq1 Neq2
    -- $5(b_0 - a_0) = 8(a_1 - b_1)$
    have eq : 5 * (b0 - a0) = 8 * (a1 - b1) := by
      rw [mul_comm 5, Nat.mul_sub, Nat.sub_mul]
      have Neq1' := Neq1
      apply Nat.sub_eq_of_eq_add at Neq1
      apply Nat.sub_eq_of_eq_add at Neq2
      rw [← Neq1, ← Neq2, ← Nat.sub_add_eq, add_comm (b1 * 8), Nat.sub_add_eq, mul_comm b1]
      have eq : N - (N - a1 * 8) = 8 * a1 := by
        refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
        exact Nat.sub_le N (a1 * 8)
        rw [← Nat.add_sub_assoc, add_comm, Nat.add_sub_assoc, mul_comm, Nat.sub_self, add_zero]
        linarith
        linarith
      rw [eq]
    -- $b_0 - a_0 \geq 8$
    have b0subge : b0 - a0 ≥ 8 := by
      have dvd : 8 ∣ (b0 - a0) := by 
        have dvd : 8 ∣ 5 * (b0 - a0) := by
          exact Dvd.intro (a1 - b1) (id (Eq.symm eq))
        have ndvd : Nat.Coprime 8 5 := by
          exact rfl
        exact Nat.Coprime.dvd_of_dvd_mul_left ndvd dvd
      exact Nat.le_of_dvd (by exact Nat.zero_lt_sub_of_lt altb) dvd
    -- $a_1 - b_1 \geq 5$
    have a1ge : 13 ≤ a1 := by
      have le1 : b1 + 5 ≤ a1 - b1 + b1 := by
        linarith
      rw [Nat.sub_add_cancel (by linarith)] at le1
      linarith
    linarith
  -- so $N \geq 104$
  rcases Nat.lt_or_gt.mp aneb with alt | blt
  exact Nge (a 0) (b 0) (a 1) (b (0 + 1)) alt (hbmono 0) Neqa Neqb
  exact Nge (b 0) (a 0) (b 1) (a (0 + 1)) blt (hamono 0) Neqb Neqa