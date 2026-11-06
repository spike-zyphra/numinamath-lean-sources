import Mathlib
/- ## Task 4.

Let $a$ and $b$ be relatively prime natural numbers different from 1. A sequence is defined as

$$
x_{1}=a, \quad x_{2}=b, \quad x_{n}=\frac{x_{n-1}^{2}+x_{n-2}^{2}}{x_{n-1}+x_{n-2}} \quad \text { for } n \geqslant 3
$$

Prove that no term $x_{n}$ of this sequence, except the first two, is a natural number. -/
theorem number_theory_250018 (x : ℕ → ℚ) (a b : ℕ) (ha : a > 1) (hb : b > 1) (hab : Nat.Coprime a b) (hn : ∀ n : ℕ, x (n + 2) = ((x (n + 1) : ℚ) ^ 2 + x n ^ 2) / (x (n + 1) + x n)) (h1 : x 0 = a) (h2 : x 1 = b) : ∀ n : ℕ, n ≥ 2 → ¬(∃ k : ℕ, x n = k):= by
  intro n hn1
  -- First, prove that all terms x_n > 1 by induction
  have h3 : ∀ n : ℕ, x n > 1 ∧ x (n + 1) > 1:= by
    intro n
    induction n with
    | zero =>
      -- Base case: x_0 = a > 1 and x_1 = b > 1
      simp [h1, h2]
      omega
    | succ n ih =>
      -- Inductive step: if x_n > 1 and x_{n+1} > 1, then x_{n+2} > 1
      rcases ih with ⟨ih1, ih2⟩
      refine ⟨ih2, ?_⟩
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [hn n]
      have g : x (n + 1) + x n > 0:= by positivity
      -- Show that numerator > denominator to prove x_{n+2} > 1
      suffices x (n + 1) ^ 2 + x n ^ 2 > x (n + 1) + x n by exact (one_lt_div g).mpr this
      have g1 : x n * x n > x n:= by
        have g1 : x n > 0:= by linarith
        exact (lt_mul_iff_one_lt_right g1).mpr ih1
      have g2 : x (n + 1) * x (n + 1) > x (n + 1):= by
        have g2 : x (n + 1) > 0:= by linarith
        exact (lt_mul_iff_one_lt_right g2).mpr ih2
      linarith
  -- Simplify to just x_n > 1 for all n
  replace h3 : ∀ n : ℕ, x n > 1:= by
    intro n
    exact (h3 n).1
  -- Define p(n) as the numerator and q(n) as the denominator of x_n in reduced form
  set p:= fun n => ((x n).num).natAbs with hp
  set q:= fun n => (x n).den with hq
  clear_value p q
  -- Show that x_n = p(n)/q(n) in reduced form
  have h4 : ∀ n : ℕ, x n = p n / q n:= by
    intro n
    rw [hp, hq]
    simp
    field_simp
    rw [show (↑(x n).num.natAbs : ℚ) = (↑(↑(x n).num.natAbs : ℤ) : ℚ) by rfl]
    simp
    suffices (x n).num = |(x n).num| by qify at this ; exact this
    suffices (x n).num ≥ 0 by exact Eq.symm (abs_of_nonneg this)
    suffices x n ≥ 0 by exact Rat.num_nonneg.mpr this
    replace h3:= h3 n
    linarith
  -- Prove that p(n) and q(n) are coprime (reduced form)
  have h5 : ∀ n : ℕ, Nat.Coprime (p n) (q n):= by
    intro n
    rw [hp, hq]
    simp
    exact (x n).reduced
  -- Key lemma: if p/q = p1/q1 in reduced form, then p|p1 and q|q1
  have h6 : ∀ p q p1 q1 : ℕ, Nat.Coprime p q → p / q = (p1 : ℚ) / (q1 : ℚ) → q1 > 0 → q > 0 → p ∣ p1 ∧ q ∣ q1:= by
    intro p q p1 q1 hpq hpq1 hq1 hq
    field_simp at hpq1
    replace hpq1 : p1 * q = p * q1:= by qify ; linarith
    refine ⟨?_, ?_⟩
    suffices p ∣ p1 * q by exact Nat.Coprime.dvd_of_dvd_mul_right hpq this
    use q1
    replace hpq : Nat.Coprime q p:= by exact Nat.coprime_comm.mp hpq
    suffices q ∣ p * q1 by exact Nat.Coprime.dvd_of_dvd_mul_left hpq this
    use p1
    linarith
  -- All denominators are positive
  have hqpos : ∀ n : ℕ, q n > 0:= by
    intro n
    simp [hq]
    exact Rat.den_pos (x n)
  -- All numerators are greater than 1 (since x_n > 1)
  have hppos : ∀ n : ℕ, p n > 1:= by
    intro n
    simp [hp]
    by_contra H
    simp at H
    replace H : (x n).num.natAbs = 0 ∨ (x n).num.natAbs = 1:= by omega
    have g : (x n).num > 0:= by
      suffices x n > 0 by exact Rat.num_pos.mpr this
      replace h3:= h3 n
      linarith
    zify at H
    rw [abs_of_pos g] at H
    replace H : (x n).num = 1:= by omega
    replace h4:= h4 n
    replace hqpos:= hqpos n
    simp [hp, hq] at h4 hqpos
    rw [H] at h4
    simp at h4
    replace h3:= h3 n
    rw [h4] at h3
    field_simp at h3
    have g1 : (x n).den ≥ 1:= by omega
    qify at g1
    replace g1 : 1 / (↑(x n).den : ℚ) ≤ 1:= by exact div_le_self rfl g1
    linarith
  -- Express the recurrence relation in terms of p and q
  have h7 : ∀ n : ℕ, (p (n + 2) : ℚ) / (q (n + 2)) = (p n ^ 2 * q (n + 1) ^ 2 + p (n + 1) ^ 2 * q n ^ 2) / (q n * q (n + 1) * (p n * q (n + 1) + p (n + 1) * q n)):= by
    intro n
    replace hn:= hn n
    simp [h4] at hn
    rw [hn]
    have g1:= hppos n
    have g2:= hppos (n + 1)
    have g3:= hqpos n
    have g4:= hqpos (n + 1)
    field_simp
    ring
  -- Prove that consecutive numerators are coprime by induction
  have h8 : ∀ n : ℕ, Nat.Coprime (p n) (p (n + 1)):= by
    intro n
    induction n with
    | zero =>
      -- Base case: p(0) = a, p(1) = b, and a,b are coprime
      have g1:= h4 0
      have g2:= h4 1
      rw [h1] at g1
      rw [h2] at g2
      have g3:= hqpos 0
      have g4:= hqpos 1
      field_simp at g1 g2
      replace g1 : a * q 0 = p 0:= by qify ; linarith
      replace g2 : b * q 1 = p 1:= by qify ; linarith
      replace g3 : q 0 = 1:= by
        replace g1 : q 0 ∣ p 0:= by rw [←g1] ; simp
        have g:= h5 0
        replace g : Nat.Coprime (q 0) (p 0):= by exact Nat.coprime_comm.mp g
        exact Nat.Coprime.eq_one_of_dvd g g1
      replace g4 : q 1 = 1:= by
        replace g2 : q 1 ∣ p 1:= by rw [←g2] ; simp
        have g:= h5 1
        replace g : Nat.Coprime (q 1) (p 1):= by exact Nat.coprime_comm.mp g
        exact Nat.Coprime.eq_one_of_dvd g g2
      rw [g3] at g1
      rw [g4] at g2
      simp at g1 g2
      rw [←g1, ←g2]
      exact hab
    | succ n ih =>
      -- Inductive step: use the recurrence relation and coprimality properties
      rw [show n + 1 + 1 = n + 2 by omega]
      replace h7:= h7 n
      replace h7:= h6 (p (n + 2)) (q (n + 2)) ((p n) ^ 2 * (q (n + 1)) ^ 2 + (p (n + 1)) ^ 2 * (q n) ^ 2) ((q n) * (q (n + 1)) * ((p n) * (q (n + 1)) + (p (n + 1)) * (q n))) (h5 (n + 2)) (by simp ; exact h7) (by have g1:= hppos n ; have g2:= hppos (n + 1) ; have g3:= hqpos n ; have g4:= hqpos (n + 1) ; positivity) (hqpos (n + 2))
      replace h7:= h7.1
      suffices Nat.Coprime (p (n + 1)) (p n ^ 2 * q (n + 1) ^ 2 + p (n + 1) ^ 2 * q n ^ 2) by exact Nat.Coprime.coprime_dvd_right h7 this
      rw [show p (n + 1) ^ 2 * q n ^ 2 = p (n + 1) * (p (n + 1) * q n ^ 2) by ring]
      suffices Nat.Coprime (p (n + 1)) (p n ^ 2 * q (n + 1) ^ 2) by exact (Nat.coprime_add_mul_left_right (p (n + 1)) (p n ^ 2 * q (n + 1) ^ 2) (p (n + 1) * q n ^ 2)).mpr this
      rw [show p n ^ 2 * q (n + 1) ^ 2 = (p n * q (n + 1)) ^ 2 by ring]
      suffices Nat.Coprime (p (n + 1)) (p n * q (n + 1)) by exact Nat.Coprime.pow_right 2 this
      replace h5:= h5 (n + 1)
      replace ih:= Nat.coprime_comm.mp ih
      exact Nat.Coprime.mul_right ih h5
  -- Set m = n - 2 to work with the recurrence relation
  set m:= n - 2 with hm
  clear_value m
  replace hm : n = m + 2:= by omega
  subst n
  clear hn1
  -- Assume for contradiction that x_{m+2} is a natural number
  by_contra H
  -- This means q(m+2) divides p(m+2)
  replace H : q (m + 2) ∣ p (m + 2):= by
    rcases H with ⟨k, hk⟩
    rw [h4 (m + 2)] at hk
    replace hqpos:= hqpos (m + 2)
    field_simp at hk
    use k
    qify
    linarith
  -- Use the recurrence relation to show divisibility properties
  replace h7:= h7 m
  replace H : (q m) * (q (m + 1)) * ((p m) * (q (m + 1)) + (p (m + 1)) * (q m)) ∣ (p m) ^ 2 * (q (m + 1)) ^ 2 + (p (m + 1)) ^ 2 * (q m) ^ 2:= by
    set y:= (q m) * (q (m + 1)) * ((p m) * (q (m + 1)) + (p (m + 1)) * (q m)) with hy
    set z:= (p m) ^ 2 * (q (m + 1)) ^ 2 + (p (m + 1)) ^ 2 * (q m) ^ 2 with hz
    clear_value y z
    replace h7 : (p (m + 2)) / (q (m + 2) : ℚ) = z / y:= by
      subst y z
      simp
      exact h7
    rcases H with ⟨k, hk⟩
    rw [hk] at h7
    simp at h7
    rw [show ↑(q (m + 2)) * ↑k / (↑(q (m + 2)) : ℚ) = k by replace hqpos:= hqpos (m + 2) ; field_simp] at h7
    have hypos : y > 0:= by
      subst y
      have g1:= hppos m
      have g2:= hppos (m + 1)
      have g3:= hqpos m
      have g4:= hqpos (m + 1)
      positivity
    field_simp at h7
    use k
    qify
    linarith
  -- Show that q(m+1)^2 divides q(m)^2
  have h9 : q (m + 1) ^ 2 ∣ q m ^ 2:= by
    have h9 : q (m + 1) ∣ q m ^ 2:= by
      replace H : q (m + 1) ∣ p m ^ 2 * q (m + 1) ^ 2 + p (m + 1) ^ 2 * q m ^ 2:= by
        have g : q (m + 1) ∣ q m * q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m):= by
          use q m * (p m * q (m + 1) + p (m + 1) * q m)
          ring
        exact Nat.dvd_trans g H
      have g : q (m + 1) ∣ p m ^ 2 * q (m + 1) ^ 2:= by
        use p m ^ 2 * q (m + 1)
        ring
      replace H : q (m + 1) ∣ p (m + 1) ^ 2 * q m ^ 2:= by exact (Nat.dvd_add_iff_right g).mpr H
      replace h5:= h5 (m + 1)
      replace h5:= Nat.coprime_comm.mp h5
      replace h5 : Nat.Coprime (q (m + 1)) (p (m + 1) ^ 2):= by exact Nat.Coprime.pow_right 2 h5
      exact Nat.Coprime.dvd_of_dvd_mul_left h5 H
    have H1 : q (m + 1) ^ 2 ∣ q m * q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m):= by
      have H1 : q (m + 1) ∣ q m * (p m * q (m + 1) + p (m + 1) * q m):= by
        rcases h9 with ⟨k, hk⟩
        use k * p (m + 1) + p m * q m
        rw [show q (m + 1) * (k * p (m + 1) + p m * q m) = q m ^ 2 * p (m + 1) + q (m + 1) * q m * p m by rw [hk] ; ring]
        ring
      replace H1 : q (m + 1) * q (m + 1) ∣ q m * (p m * q (m + 1) + p (m + 1) * q m) * q (m + 1):= by exact Nat.mul_dvd_mul_right H1 (q (m + 1))
      rcases H1 with ⟨k, hk⟩
      use k
      linarith only [hk]
    replace H1 : q (m + 1) ^ 2 ∣ p m ^ 2 * q (m + 1) ^ 2 + p (m + 1) ^ 2 * q m ^ 2:= by exact Nat.dvd_trans H1 H
    have g : q (m + 1) ^ 2 ∣ p m ^ 2 * q (m + 1) ^ 2:= by simp
    replace H1 : q (m + 1) ^ 2 ∣ p (m + 1) ^ 2 * q m ^ 2:= by exact (Nat.dvd_add_iff_right g).mpr H1
    replace h5:= h5 (m + 1)
    replace h5:= Nat.coprime_comm.mp h5
    replace h5 : Nat.Coprime (q (m + 1) ^ 2) (p (m + 1) ^ 2):= by exact Nat.Coprime.pow 2 2 h5
    exact Nat.Coprime.dvd_of_dvd_mul_left h5 H1
  -- Show that q(m)^2 divides q(m+1)^2 (mutual divisibility)
  have h10 : q m ^ 2 ∣ q (m + 1) ^ 2:= by
    have h10 : q m ∣ q (m + 1) ^ 2:= by
      replace H : q m ∣ p m ^ 2 * q (m + 1) ^ 2 + p (m + 1) ^ 2 * q m ^ 2:= by
        have g : q m ∣ q m * q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m):= by
          use q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m)
          ring
        exact Nat.dvd_trans g H
      have g : q m ∣ p (m + 1) ^ 2 * q m ^ 2:= by
        use p (m + 1) ^ 2 * q m
        ring
      replace H : q m ∣ p m ^ 2 * q (m + 1) ^ 2:= by exact (Nat.dvd_add_iff_left g).mpr H
      replace h5:= h5 m
      replace h5:= Nat.coprime_comm.mp h5
      replace h5 : Nat.Coprime (q m) (p m ^ 2):= by exact Nat.Coprime.pow_right 2 h5
      exact Nat.Coprime.dvd_of_dvd_mul_left h5 H
    have H1 : q m ^ 2 ∣ q m * q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m):= by
      rw [show q m ^ 2 = q m * q m by ring]
      rw [show q m * q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m) = q m * (q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m)) by ring]
      suffices q m ∣ q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m) by exact Nat.mul_dvd_mul_left (q m) this
      rw [show q (m + 1) * (p m * q (m + 1) + p (m + 1) * q m) = q (m + 1) ^ 2 * p m + q m * (q (m + 1) * p (m + 1)) by ring]
      have g1 : q m ∣ q (m + 1) ^ 2 * p m:= by exact Dvd.dvd.mul_right h10 (p m)
      have g2 : q m ∣ q m * (q (m + 1) * p (m + 1)):= by simp
      exact (Nat.dvd_add_iff_right g1).mp g2
    replace H1 : q m ^ 2 ∣ p m ^ 2 * q (m + 1) ^ 2 + p (m + 1) ^ 2 * q m ^ 2:= by exact Nat.dvd_trans H1 H
    have g : q m ^ 2 ∣ p (m + 1) ^ 2 * q m ^ 2:= by simp
    replace H1 : q m ^ 2 ∣ p m ^ 2 * q (m + 1) ^ 2:= by exact (Nat.dvd_add_iff_left g).mpr H1
    replace h5:= h5 m
    replace h5:= Nat.coprime_comm.mp h5
    replace h5 : Nat.Coprime (q m ^ 2) (p m ^ 2):= by exact Nat.Coprime.pow 2 2 h5
    exact Nat.Coprime.dvd_of_dvd_mul_left h5 H1
  -- Since q(m)^2 | q(m+1)^2 and q(m+1)^2 | q(m)^2, we have q(m) = q(m+1)
  replace h9:= (Nat.pow_dvd_pow_iff (by omega)).mp h9
  replace h10:= (Nat.pow_dvd_pow_iff (by omega)).mp h10
  replace h9 : q m = q (m + 1):= by exact Nat.dvd_antisymm h10 h9
  -- Substitute q(m) = q(m+1) back into the divisibility condition
  rw [h9] at H
  rw [show q (m + 1) * q (m + 1) * (p m * q (m + 1) + p (m + 1) * q (m + 1)) = q (m + 1) ^ 2 * (q (m + 1) * (p m + p (m + 1))) by ring] at H
  rw [show p m ^ 2 * q (m + 1) ^ 2 + p (m + 1) ^ 2 * q (m + 1) ^ 2 = q (m + 1) ^ 2 * (p m ^ 2 + p (m + 1) ^ 2) by ring] at H
  -- This implies q(m+1) * (p(m) + p(m+1)) divides p(m)^2 + p(m+1)^2
  replace H : (q (m + 1) * (p m + p (m + 1))) ∣ p m ^ 2 + p (m + 1) ^ 2:= by
    have g : q (m + 1) ^ 2 > 0:= by
      replace hqpos:= hqpos (m + 1)
      positivity
    exact Nat.dvd_of_mul_dvd_mul_left g H
  -- Since q(m+1) and p(m+1) are coprime, this reduces to p(m) + p(m+1) divides p(m)^2 + p(m+1)^2
  replace H : p m + p (m + 1) ∣ p m ^ 2 + p (m + 1) ^ 2:= by exact dvd_of_mul_left_dvd H
  -- Add 2*p(m)*p(m+1) to both sides to get a perfect square
  have H1 : p m + p (m + 1) ∣ p m ^ 2 + p (m + 1) ^ 2 + 2 * p m * p (m + 1):= by
    use p m + p (m + 1)
    ring
  -- This implies p(m) + p(m+1) divides 2*p(m)*p(m+1)
  replace H : p m + p (m + 1) ∣ 2 * p m * p (m + 1):= by exact (Nat.dvd_add_iff_right H).mpr H1
  -- Use coprimality of p(m) and p(m+1) to show p(m) + p(m+1) divides 2
  replace h8:= h8 m
  replace h9 : Nat.Coprime (p m + p (m + 1) * 1) (p (m + 1)):= by exact (Nat.coprime_add_mul_left_left (p m) (p (m + 1)) 1).mpr h8
  rw [show p m + p (m + 1) * 1 = p m + p (m + 1) by simp] at h9
  replace h8 : Nat.Coprime (p m) (p m * 1 + p (m + 1)):= by exact (Nat.coprime_mul_left_add_right (p m) (p (m + 1)) 1).mpr h8
  replace h8:= Nat.coprime_comm.mp h8
  rw [show p m * 1 + p (m + 1) = p m + p (m + 1) by simp] at h8
  replace h8 : Nat.Coprime (p m + p (m + 1)) (p m * p (m + 1)):= by exact Nat.Coprime.mul_right h8 h9
  rw [show 2 * p m * p (m + 1) = 2 * (p m * p (m + 1)) by ring] at H
  replace H : p m + p (m + 1) ∣ 2:= by exact Nat.Coprime.dvd_of_dvd_mul_right h8 H
  -- Since p(m) + p(m+1) > 2 (both p(m), p(m+1) > 1), this is a contradiction
  apply Nat.le_of_dvd (by omega) at H
  have g1:= hppos m
  have g2:= hppos (m + 1)
  linarith
