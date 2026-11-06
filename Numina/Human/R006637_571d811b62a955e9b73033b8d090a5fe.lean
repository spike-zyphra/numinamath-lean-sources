import Mathlib
/- Let $M$ be a positive integer. Let $q = M \div 13$ be the integer quotient of $M$ by $13$, and $r = M \pmod{13}$ be the remainder.
Show that the sum $S = \sum_{k=1}^{M} \lfloor \frac{6k}{13} \rfloor$ is equal to $78 \frac{q(q-1)}{2} + 36q + 6rq + \sum_{k=1}^{r} \lfloor \frac{6k}{13} \rfloor$.
(Note: If $q=0$, the term $\frac{q(q-1)}{2}$ is $0$. If $r=0$, the sum $\sum_{k=1}^{r}$ is $0$.) -/
theorem number_theory_639504 (q r m : ℕ) (hm : m > 0) (hr : r = m % 13) (hq : m = 13 * q + r) : ∑ i in Finset.range m, (6 * (i + 1)) / 13 = 78 * q * (q - 1) / 2 + 36 * q + 6 * r * q + ∑ i in Finset.range r, (6 * (i + 1)) / 13:= by
  -- Substitute m with 13q + r using the hypothesis hq
  subst m

  -- Prove that q(q-1) is divisible by 2
  have h : 2 ∣ q * (q - 1):= by
    by_cases hq : q = 0
    .
      subst q
      simp
    .
      set t:= q - 1 with ht
      clear_value t
      replace ht : q = t + 1:= by omega
      subst q
      by_cases ht : Odd t
      .
        have g : Odd 1:= by decide
        replace g : Even (t + 1):= by exact Odd.add_odd ht g
        replace g : 2 ∣ t + 1:= by exact even_iff_two_dvd.mp g
        exact Dvd.dvd.mul_right g t
      .
        simp at ht
        replace ht : 2 ∣ t:= by exact even_iff_two_dvd.mp ht
        exact Dvd.dvd.mul_left ht (t + 1)

  -- Simplify the fraction 78q(q-1)/2 to 39q(q-1)
  replace h : 78 * q * (q - 1) / 2 = 39 * q * (q - 1):= by
    rcases h with ⟨t, ht⟩
    rw [show 78 * q * (q - 1) = (78 * t) * 2 by linarith]
    rw [show 39 * q * (q - 1) = 78 * t by linarith]
    omega
  rw [h]

  -- Prove that r < 13 using the remainder property
  replace hr : r < 13:= by
    rw [hr]
    refine Nat.mod_lt (13 * q + r) (by omega)

  -- Main inductive proof showing the sum formula holds for all q
  have h1 : ∀ q : ℕ, ∑ i ∈ Finset.range (13 * q + r), 6 * (i + 1) / 13 = 39 * q * (q - 1) + 36 * q + 6 * r * q + ∑ i ∈ Finset.range r, 6 * (i + 1) / 13:= by
    intro q
    induction q with
    | zero =>
      simp
    | succ q ih =>
      rw [show 13 * (q + 1) + r = 13 * q + r + 13 by omega]
      repeat rw [Finset.sum_range_succ]
      rw [ih]

      -- Helper lemma for simplifying division expressions
      have h1 : ∀ n : ℕ, 6 * (13 * q + r + n + 1) / 13 = 6 * q + 6 * (r + n + 1) / 13:= by
        intro n
        rw [show 13 * q + r + n + 1 = 13 * q + (r + n + 1) by ring]
        set k:= r + n + 1 with hk
        clear_value k
        rw [show 6 * (13 * q + k) = 13 * (6 * q) + 6 * k by omega]
        refine Nat.mul_add_div (by omega) (6 * q) (6 * k)
      repeat rw [h1 _]
      rw [show q + 1 - 1 = q by omega]

      -- Algebraic manipulation to complete the inductive step
      have h2 : 39 * (q + 1) * q = 39 * q * (q - 1) + 78 * q:= by
        by_cases hq : q = 0
        .
          subst q
          simp
        .
          rw [show q + 1 = q - 1 + 2 by omega]
          linarith
      rw [h2]
      suffices 6 * (13 * q + r + 1) / 13 + (6 * q + 6 * (r + 1 + 1) / 13) + (6 * q + 6 * (r + 2 + 1) / 13) + (6 * q + 6 * (r + 3 + 1) / 13) + (6 * q + 6 * (r + 4 + 1) / 13) + (6 * q + 6 * (r + 5 + 1) / 13) + (6 * q + 6 * (r + 6 + 1) / 13) + (6 * q + 6 * (r + 7 + 1) / 13) + (6 * q + 6 * (r + 8 + 1) / 13) + (6 * q + 6 * (r + 9 + 1) / 13) + (6 * q + 6 * (r + 10 + 1) / 13) + (6 * q + 6 * (r + 11 + 1) / 13) + (6 * q + 6 * (r + 12 + 1) / 13) = 78 * q + 36 + 6 * r by linarith
      replace h1:= h1 0
      rw [show 13 * q + r + 0 + 1 = 13 * q + r + 1 by omega]
      rw [h1]
      suffices 6 * (r + 0 + 1) / 13 + 6 * (r + 1 + 1) / 13 + 6 * (r + 2 + 1) / 13 + 6 * (r + 3 + 1) / 13 + 6 * (r + 4 + 1) / 13 + 6 * (r + 5 + 1) / 13 + 6 * (r + 6 + 1) / 13 + 6 * (r + 7 + 1) / 13 + 6 * (r + 8 + 1) / 13 + 6 * (r + 9 + 1) / 13 + 6 * (r + 10 + 1) / 13 + 6 * (r + 11 + 1) / 13 + 6 * (r + 12 + 1) / 13 = 36 + 6 * r by linarith
      replace hr : r ∈ Finset.range 13:= by
        simp
        exact hr
      fin_cases hr
      all_goals
        norm_num
  exact h1 q
