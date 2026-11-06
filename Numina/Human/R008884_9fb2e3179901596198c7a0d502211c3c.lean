import Mathlib

open Finset Nat Int GCDMonoid

/-
Corollary 3.2 states that if \( a \equiv b \mod m_1 \), \( a \equiv b \mod m_2 \), ..., \( a \equiv b \mod m_k \), where \( a \) and \( b \) are integers and \( m_1, m_2, \ldots, m_k \) are relatively prime positive integers, then it follows that \( a \equiv b \mod (m_1 m_2 \cdots m_k) \).
-/
theorem number_theory_4647 (k : ℕ) (a b : ℤ) (m : Fin k → ℕ) (h₀ : 0 < k)
                    (h₁ : ∀ i : Fin k, m i > 0)
                    (hrel : ∀ i j : Fin k, i ≠ j → Nat.Coprime (m i) (m j))
                    (h₂ : ∀ i : Fin k, a ≡ b [ZMOD m i]) :
                    a ≡ b [ZMOD ∏ i, m i] := by
  -- To prove this statement, we need to use mathematical induction on \( k \).
  induction k with
  | zero =>
    -- When \( k = 0 \), this statement is trivially true.
    simp_all
  | succ n h =>
    -- Now, we assume that the statement holds for \( k = n \), and we need to prove it for \( k = n + 1 \).
    -- That is, we need to prove \( a \equiv b \mod \prod_{i=1}^{n+1} m_i \).
    norm_cast
    -- Clearly, \( \prod_{i=1}^{n+1} m_i = \prod_{i=1}^n m_i \cdot m_{n+1} \).
    rw [Fin.prod_univ_castSucc]
    rw [← Fin.prod_ofFn]
    -- Next, we need to prove that \( \prod_{i=1}^n m_i \) and \( m_{n+1} \) are coprime.
    have : (List.ofFn fun i => m i.castSucc).prod.Coprime (m (Fin.last n)) := by
      -- Therefore, we only need to prove that \( m_i \) and \( m_{n+1} \) are coprime for \( i < n+1 \).
      -- This can be clearly obtained from the conditions of the problem.
      apply Nat.coprime_list_prod_left_iff.mpr
      simp
      intro j
      apply hrel
      have := Fin.castSucc_lt_last j
      aesop
    -- Since we have proven that \( \prod_{i=1}^n m_i \) and \( m_{n+1} \) are coprime,
    -- our goal can be transformed into \( a \equiv b \mod \lcm(\prod_{i=1}^n m_i, m_{n+1}) \).
    rw [← Nat.Coprime.lcm_eq_mul this]
    apply Int.modEq_of_dvd
    rw [Int.natCast_dvd]
    -- Therefore, we now only need to prove \( a \equiv b \mod \prod_{i=1}^n m_i \) and \( a \equiv b \mod m_{n+1} \).
    apply Nat.lcm_dvd
    · -- For the first subgoal, since we used mathematical induction, the statement holds when \( k = n \).
      let m' := fun (i : Fin n) => m i.castSucc
      cases Nat.eq_zero_or_pos n with
      | inl hn => simp_all
      | inr hnpos =>
        have hpos' : ∀ i : Fin n, m' i > 0 := fun i => h₁ i.castSucc
        have hcoprime' : ∀ (i j : Fin n), i ≠ j → (m' i).Coprime (m' j) := by
          intro i j hij
          have : i.castSucc ≠ j.castSucc := by simp_all
          exact hrel i.castSucc j.castSucc this
        have hmod' : ∀ i : Fin n, a ≡ b [ZMOD (m' i)] := fun i => h₂ i.castSucc
        have := Int.ModEq.dvd (h m' (by linarith) hpos' hcoprime' hmod')
        norm_cast at this
        rw [← Fin.prod_ofFn,Int.natCast_dvd] at this
        exact this
    · -- For the second subgoal, the statement is clearly true.
      exact Int.natCast_dvd.mp <| Int.ModEq.dvd (h₂ (Fin.last n))
    -- In summary, the inductive step is completed.
    -- Therefore, by mathematical induction, this statement is proved.
