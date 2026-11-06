import Mathlib

/- In a sequence $u_{0}, u_{1}, \ldots$ of positive integers, $u_{0}$ is arbitrary, and for any non-negative integer $n$,

$$
u_{n+1}= \begin{cases}\frac{1}{2} u_{n} & \text { for even } u_{n} \\ a+u_{n} & \text { for odd } u_{n}\end{cases}
$$

where $a$ is a fixed odd positive integer. Prove that the sequence is periodic from a certain step. -/
theorem number_theory_238809 (a : ℕ) (ha : Odd a ∧ a > 0) (u : ℕ → ℕ)
    (hu0 : u 0 > 0) (hun : ∀ n, u (n + 1) = if Even (u n) then (u n) / 2 else a + u n) :
    ∃ N, ∃ T > 0, ∀ n ≥ N, u (n + T) = u n := by
  rcases ha with ⟨ha₁, ha₂⟩
  -- Actually, as long as we can find a single pair of N and T such that u (N + T) = u N, we can show that the sequence is periodic from N
  -- Since one term of the sequence is determined by the previous term, we can show that the sequence is periodic from N.
  suffices H : ∃ N, ∃ T > 0, u (N + T) = u N by
    rcases H with ⟨N, T, hT, h₁⟩
    refine ⟨N, T, hT, fun n hn => ?_⟩
    -- We show that u (n + T) = u n by induction.
    induction n, hn using Nat.le_induction with
    | base => exact h₁
    | succ n hn ih => rw [show n + 1 + T = n + T + 1 by ring, hun, hun, ih]
  -- We show that u n ≤ a for infinitely many n.
  have H : {n : ℕ | u n ≤ a}.Infinite := by
    -- It suffices to show that the set is not bounded above.
    refine Set.infinite_of_not_bddAbove fun H => ?_
    -- If it is bounded above, then there exists some N, such that u n ≤ a implies n ≤ N.
    simp [BddAbove, Set.Nonempty, upperBounds] at H
    rcases H with ⟨N, hN⟩
    -- Let's pick the smallest a n (n > N)
    -- Set b be the infimum of the set {u n | n > N}
    set b := sInf {u n | n > N} with hb
    -- By principle of least number, b is an element of the set.
    have h : b ∈ {u n | n > N} := Nat.sInf_mem (s := {u n | n > N}) (⟨u (N + 1), N + 1, by simp⟩)
    -- We have n such that u n = b
    rcases h with ⟨n, hn, hb₂⟩
    -- We have u n > a by our assumption of contradiction.
    have hb₃ : u n > a := by
      contrapose! hn with hb₂
      exact hN hb₂
    -- The terms after u n are all no greater than u n by definition of u n
    have hb₄ (m : ℕ) (hm : m > n) : u n ≤ u m := by
      have hb₄ := Nat.sInf_le (s := {u n | n > N}) (show u m ∈ {u n | n > N} from ⟨m, hn.trans hm, rfl⟩)
      rwa [← hb, ← hb₂] at hb₄
    -- Let's consider the parity of u n
    rcases Nat.even_or_odd (u n) with heven | hodd
    . -- If u n is even, then u (n + 1) = u n / 2 < u n
      -- Contradicts the fact that u n ≤ u (n + 1)
      specialize hun n
      simp [heven] at hun
      specialize hb₄ (n + 1) (by simp)
      omega
    . -- If u n is odd, then u (n + 1) = a + u n
      -- u (n + 2) = (a + u n) / 2 < u n
      -- Contradicts the fact that u n ≤ u (n + 2)
      have huns : u (n + 1) = a + u n := by
        specialize hun n
        simpa [Nat.not_even_iff_odd.mpr hodd] using hun
      specialize hun (n + 1)
      simp [show Even (u (n + 1)) from huns.symm ▸ Odd.add_odd ha₁ hodd] at hun
      specialize hb₄ (n + 1 + 1) (by omega)
      omega
  -- There are infinitely many n such that u n ≤ a, but there are only finitely many values ≤ a.
  -- So there exists some n < m such that u n = u m (Infinite version of pigeonhole principle)
  obtain ⟨n, -, m, -, hnm, heq⟩ := Set.Infinite.exists_lt_map_eq_of_mapsTo H (f := u) (t := {x : ℕ | x ≤ a}) (by intro; simp) (Set.finite_le_nat a)
  -- And we are done,
  refine ⟨n, m - n, by omega, ?_⟩
  convert heq.symm
  omega
