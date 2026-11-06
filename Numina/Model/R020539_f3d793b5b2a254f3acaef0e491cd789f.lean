import Mathlib

theorem number_theory_220867 (a : ℕ → ℕ) (h : ∀ i j, i ≠ j → Nat.gcd (a i) (a j) = Nat.gcd i j) :
    ∀ i, a i = i := by
  intro i
  have h1 : ∀ (k : ℕ), k ≠ 0 → Nat.gcd (a k) (a 0) = Nat.gcd k 0 := by
    intro k hk
    have h2 := h k 0 (by
      omega
    )
    simpa using h2

  have h2 : a 0 = 0 := by
    have h3 : ∀ (k : ℕ), k > 0 → k ∣ a 0 := by
      intro k hk
      have h4 : Nat.gcd (a k) (a 0) = Nat.gcd k 0 := h1 k (by omega)
      have h5 : Nat.gcd k 0 = k := by
        simp
      have h6 : Nat.gcd (a k) (a 0) = k := by
        rw [h4, h5]
      have h7 : k ∣ a 0 := by
        have h8 : Nat.gcd (a k) (a 0) ∣ a 0 := by
          exact Nat.gcd_dvd_right (a k) (a 0)
        rw [h6] at h8
        exact h8
      exact h7
    -- Now to show $a_0 = 0$.
    -- Given that for all $k > 0$, $k$ divides $a_0$.
    -- Let's take $k = a_0 + 1$. If $a_0 > 0$, then $a_0 + 1 > 1$.
    -- $a_0 + 1$ divides $a_0$.
    -- But $a_0 + 1$ is greater than $a_0$, so it's a contradiction.
    by_cases h8 : a 0 > 0
    · -- Assume a 0 > 0, we derive a contradiction
      have h9 : a 0 + 1 ∣ a 0 := by
        apply h3 (a 0 + 1)
        omega
      -- If $a_0 + 1$ divides $a_0$, then $a_0 + 1 \leq a_0$.
      have h10 : a 0 + 1 ≤ a 0 := by
        exact Nat.le_of_dvd (by linarith) h9
      -- This is a contradiction because $a_0 + 1 > a_0$.
      omega
    · -- a 0 = 0
      omega

  -- Next, to show $a_i = i$ for all $i$.
  -- To show $a_i = i$, we can use the condition with $j = 0$ and $i$.
  -- $\gcd(a_i, a_0) = \gcd(i, 0)$.
  -- But $a_0 = 0$, so $\gcd(a_i, 0) = \gcd(i, 0)$.
  -- But $\gcd(a_i, 0) = a_i$ and $\gcd(i, 0) = i$.
  -- So $a_i = i$.
  have h3 : ∀ i, a i = i := by
    intro i
    have h4 : Nat.gcd (a i) (a 0) = Nat.gcd i 0 := by
      by_cases h5 : i = 0
      · -- i = 0
        rw [h5]
        all_goals
          simp [h2]
      · -- i ≠ 0
        have h7 : i ≠ 0 := by
          intro h8
          apply h5
          all_goals omega
        -- So for $i \neq 0$, we can set $j = 0$.
        -- $\gcd(a_i, a_0) = \gcd(i, 0)$.
        have h8 : Nat.gcd (a i) (a 0) = Nat.gcd i 0 := h1 i (by
          have : i ≠ 0 := h7
          omega
        )
        exact h8

    have h5 : Nat.gcd (a i) (a 0) = a i := by
      rw [show a 0 = 0 by exact h2]
      simp

    have h6 : Nat.gcd i 0 = i := by
      simp

    rw [h5, h6] at h4
    linarith

  exact h3 i