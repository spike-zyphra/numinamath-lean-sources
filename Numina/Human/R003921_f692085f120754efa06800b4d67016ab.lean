import Mathlib

/- ## Task A-1.5.

Friends Anica and Neda are playing a game where, in each move, after one of them says a number $n$, the other must say a number of the form $a \cdot b$ where $a$ and $b$ are natural numbers such that $a + b = n$. The game then continues in the same way, from the number just spoken. With which numbers could the game have started if, after some time, one of them said the number 2011? -/
theorem number_theory_222398: (∃ ns: ℕ → ℕ, (∀ t, ∃ a b, ns (t + 1) = a * b ∧  a + b = ns t) ∧ ns 0 = n₀ ∧ ∃ k, ns k = 2011) ↔ n₀ ≥ 5 := by
  let game := fun n : ℕ → ℕ ↦ ∀ t, ∃ a b, n (t+1) =a * b ∧  a + b = n t
  let reachable := fun n₀ n₁ : ℕ ↦ ∃ ns, game ns ∧ ns 0 = n₀ ∧ ∃ k, ns k = n₁

  /- Notice that with the move $$n = (n-1)+1 \mapsto (n-1)\cdot 1 = n-1$$ the spoken number decreases exactly by 1, so by a sequence of such moves, the spoken number can be decreased at will.-/
  have h1 : ∀ n₀ n₁, n₀ ≥ n₁ → reachable n₀ n₁ := by
    intro n₀ n₁ h
    let ns := fun t => n₀ - t
    have hgame : game ns := by
      intro t
      cases Nat.eq_zero_or_pos (n₀ - t) with
      | inl heq =>
        use 0,0
        simp [ns]
        omega
      | inr hpos =>
        use n₀ - (t+1), 1
        simp [ns]
        omega
    use ns
    simp_all [ns]
    use n₀ - n₁
    omega
  /- With the move
  $$n=(n−2)+2 \mapsto(n−2) \cdot2=2n−4$$
  the spoken number $n$ increases if $2n−4>n$, i.e., if $n>4$.
  When starting with $n = 5$, we can reach the number $2 ^ n + 4$ by repeating this move $n$ times.-/
  have h2 : ∀ n, reachable 5 (2 ^ n + 4) := by
    let ns := fun t : ℕ ↦ 2 ^ t + 4
    have : game ns := by
      intro t
      use 2 ^ t + 2, 2
      simp [ns]
      omega
    intro n
    use ns
    simp_all [ns]
  -- Note that the reachability relation is transitive, since we can chain different games together.
  have : IsTrans _ reachable := by
    apply IsTrans.mk
    intro n1 n2 n3 h12 h23
    rcases h12 with ⟨ns1, hgame1, rfl, k1, rfl⟩
    rcases h23 with ⟨ns2, hgame2, heq, k2, rfl⟩
    let ns := fun n ↦ if n < k1 then ns1 n else ns2 (n - k1)
    have : game ns := by
      intro n
      cases lt_or_le n k1 with
      | inl hn =>
        have ⟨a,b,h1,h2⟩ := hgame1 n
        use a, b
        simp_all [ns]
        intro hn'
        have heq' : k1 = n + 1 := by linarith
        subst heq'
        simp
        rw[heq]
        exact h1
      | inr h =>
        have ⟨a,b,h1,h2⟩ := hgame2 (n- k1)
        use a, b
        simp [ns]
        repeat rw [if_neg (by linarith)]
        have : n - k1 + 1 = n + 1 - k1 := by omega
        simp_all
    use ns
    simp_all [ns]
    use k1 + k2
    simp_all
  /- Starting from any number $n>4$, by repeating that move, we can reach some number greater than 2011,and then by decreasing as described above, we can obtain the number 2011.
  -/
  have h3 : ∀ n > 4, ∀ m, reachable n m := by
    intro n hn m
    apply IsTrans.trans n 5 m
    · exact h1 n 5 (by linarith)
    apply IsTrans.trans 5 (2^ m + 4) m
    · exact h2 m
    · have h : 2 ^ m + 4 > m := by calc
        2 ^ m + 4 ≥ 2 ^ m := by linarith
        _         > m     := by simp [Nat.lt_two_pow_self]
      exact h1 (2^m + 4) m (by linarith)
  /- Notice that the numbers 1,2,3,4 cannot be increased with allowed moves:
    \begin{align*}
      & 2=1+1 && 1\cdot 1=1 && 3=2+1 &&2 \cdot 1=2\\
      & 4=3+1 && 3 \cdot 1=3 && 4=2+2 &&2 \cdot 2=2
    \end{align*}
    so starting from them, we cannot reach the number 2011.
  -/
  have h4 : ∀ ns, game ns ∧ ns 0 < 5 → ∀ t, ns t < 5 := by
    rintro ns ⟨hgame, hns⟩ t
    induction t with
    | zero => exact hns
    | succ t' ih =>
      have ⟨a, b, h1, h2⟩ : ∃ a b, ns (t' + 1) =a * b ∧  a + b = ns t' := hgame t'
      have ha : a < 5 := by linarith
      have hb : b < 5 := by linarith
      interval_cases a
      all_goals
        interval_cases b
      all_goals
        simp_all
      all_goals
        linarith
  -- Therefore, the game could have started with any number $n$ that satisfies $n \geq 5$.
  apply Iff.intro
  · intro h --  h : reachable n₀ 2011
    rcases h with ⟨ns, hgame, rfl, k, hnsk⟩
    by_contra h'
    simp at h'
    have : ns k < 5 := h4 ns ⟨hgame, h'⟩ k
    linarith
  · intro hn₀
    show reachable n₀ 2011
    apply h3 n₀ (by linarith)