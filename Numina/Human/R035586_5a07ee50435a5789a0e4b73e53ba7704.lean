import Mathlib

/- A sequence of positive integers is given by $a_{1}=1$ and $a_{n}=\operatorname{gcd}\left(a_{n-1}, n\right)+1$ for $n>1$. Calculate $a_{2002}$.-/
theorem number_theory_611063 (a : ℕ → ℕ) (ha₀ : a 1 = 1) (ha : ∀ n > 1, a n = Nat.gcd (a (n - 1)) n + 1) : a 2002 = 3 := by
  -- We first show that a_n > 0 for all n > 0.
  have h₀ : ∀ n, a (n + 1) > 0 := by
    intro n
    induction n with
    | zero =>
      simp [ha₀]
    | succ n hn =>
      rw [ha _ (by omega)]
      apply Nat.succ_pos
  -- We first show that a_n ≤ n for all n > 0.
  have h₁ : ∀ n, a (n + 1) ≤ n + 1 := by
    intro n
    induction n with
    | zero =>
      simp [ha₀]
    | succ n hn =>
      rw [ha _ (by omega), Nat.add_sub_cancel]
      apply Nat.succ_le_succ
      calc
        Nat.gcd (a (n + 1)) ((n + 1) + 1) ≤ a (n + 1) := by
          apply Nat.gcd_le_left
          -- Verify that a (n + 1) > 0.
          by_cases hn : n = 0
          . simp [hn, ha₀]
          . rw [ha]
            simp
            omega
        _ ≤ (n + 1) := hn
  -- Since 1999 is a prime, we have a₁₉₉₉ = 2 or 2000, the latter is impossible.
  have h₂ : a 1999 = 2 ∨ a 1999 = 2000 := by
    specialize ha 1999 (by norm_num)
    simp at ha
    -- Let m = (a 1998, 1999).
    let m := Nat.gcd (a 1998) 1999
    -- We have m | 1999.
    have hm : m ∣ 1999 := by
      simp [m]
      apply Nat.gcd_dvd_right
    -- Since 1999 is a prime, m = 1 or 1999.
    apply Nat.Prime.eq_one_or_self_of_dvd (show Nat.Prime 1999 by norm_num) at hm
    rw [show Nat.gcd (a 1998) 1999 = m from rfl] at ha
    omega
  simp [show ¬a 1999 = 2000 by specialize h₁ 1998; simp at h₁; omega] at h₂
  -- Now calculate a 2002.
  rw [ha, ha, ha]
  simp [h₂]
  all_goals
    norm_num
