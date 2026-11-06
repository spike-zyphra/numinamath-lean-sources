import Mathlib
/- Let $m$ be an odd natural number such that $m \ge 3$ and $m+1$ is not divisible by $3$. Let $N = m(m+1)$.
Let $y_3$ be the modular inverse of $3$ modulo $m+1$, specifically an integer in the range $1 \le y_641431 \le m$.
Let $y_4$ be the modular inverse of $4$ modulo $m$, specifically an integer in the range $1 \le y_641431 \le m-1$.
Consider the expression $2 \cdot (m-2)^{-1} + (m+1) \cdot (m+4)^{-1} \pmod N$.
Show that the value of this expression, reduced to an integer in the range $[0, N-1]$, is equal to $(y_4-1) + m \cdot K$, where $K = (2y_641431 + y_641431 - 1) \pmod{m+1}$ is an integer in the range $[0, m]$. -/
theorem number_theory_641431 (m a b c d x y : ℕ) (h1 : Odd m) (h2 : m ≥ 3) (h3 : ¬(3 ∣ m + 1)) (ha : a * 3 ≡ 1 [MOD (m + 1)]) (hb : b * 4 ≡ 1 [MOD m]) (hc : c * (m - 2) ≡ 1 [MOD (m * (m + 1))]) (hd : d * (m + 4) ≡ 1 [MOD (m * (m + 1))]) (hx : x = a % (m + 1)) (hy : y = b % m) : (2 * c + (m + 1) * d) % (m * (m + 1)) = y - 1 + m * ((2 * x + y - 1) % (m + 1)):= by
  -- Clear unnecessary hypothesis
  clear h3

  -- Establish modular equivalence between x and a mod (m+1)
  have h3 : x ≡ a [MOD (m + 1)]:= by
    subst x
    exact Nat.mod_modEq a (m + 1)

  -- Establish modular equivalence between y and b mod m
  have h4 : y ≡ b [MOD m]:= by
    subst y
    exact Nat.mod_modEq b m

  -- Multiply both sides by 3 and 4 respectively to maintain equivalence
  replace h3 : x * 3 ≡ a * 3 [MOD (m + 1)]:= by exact Nat.ModEq.mul h3 rfl
  replace h4 : y * 4 ≡ b * 4 [MOD m]:= by exact Nat.ModEq.mul h4 rfl

  -- Use transitivity to show x*3 ≡ 1 (mod m+1) and y*4 ≡ 1 (mod m)
  replace h3 : x * 3 ≡ 1 [MOD (m + 1)]:= by exact Nat.ModEq.trans h3 ha
  replace h4 : y * 4 ≡ 1 [MOD m]:= by exact Nat.ModEq.trans h4 hb

  -- Show x < m+1 and y < m using modulo properties
  replace hx : x < m + 1:= by
    subst x
    refine Nat.mod_lt a (by omega)
  replace hy : y < m:= by
    subst y
    refine Nat.mod_lt b (by omega)

  -- Clear unnecessary hypotheses
  clear ha hb a b

  -- Prove x and y are positive using contradiction
  have hx1 : x > 0:= by
    by_contra H
    simp at H
    subst x
    simp at h3
    replace h3 : m + 1 ∣ 1:= by exact Nat.dvd_of_mod_eq_zero (id (Nat.ModEq.symm h3))
    simp at h3
    linarith
  have hy1 : y > 0:= by
    by_contra H
    simp at H
    subst y
    simp at h4
    replace h4 : m ∣ 1:= by exact Nat.dvd_of_mod_eq_zero (id (Nat.ModEq.symm h4))
    simp at h4
    linarith

  -- Prove first part: congruence modulo (m+1)
  have g1 : (2 * c + (m + 1) * d) % (m + 1) = (y - 1 + m * ((2 * x + y - 1) % (m + 1))) % (m + 1):= by
    -- Show (m+1)*d ≡ 0 (mod m+1)
    have g1 : (2 * c + (m + 1) * d) % (m + 1) = (2 * c) % (m + 1):= by
      have g1 : (m + 1) * d ≡ 0 [MOD (m + 1)]:= by
        suffices m + 1 ∣ (m + 1) * d by exact Nat.modEq_zero_iff_dvd.mpr this
        simp
      replace g1 : 2 * c + (m + 1) * d ≡ 2 * c + 0 [MOD (m + 1)]:= by exact Nat.ModEq.add rfl g1
      simp at g1
      exact g1
    rw [g1]

    -- Show equivalence of expressions modulo (m+1)
    have g2 : y - 1 + m * ((2 * x + y - 1) % (m + 1)) ≡ y - 1+ m * (2 * x + y - 1) [MOD (m + 1)]:= by
      have g2 : (2 * x + y - 1) % (m + 1) ≡ (2 * x + y - 1) [MOD (m + 1)]:= by exact Nat.mod_modEq (2 * x + y - 1) (m + 1)
      replace g2 : m * ((2 * x + y - 1) % (m + 1)) ≡ m * (2 * x + y - 1) [MOD (m + 1)]:= by exact Nat.ModEq.mul rfl g2
      exact Nat.ModEq.add_left (y - 1) g2
    rw [g2]

    -- Continue with modular arithmetic manipulations
    suffices 2 * c ≡ (y - 1 + m * (2 * x + y - 1)) [MOD (m + 1)] by exact this
    suffices 2 * c + m ≡ y - 1 + m * (2 * x + y - 1) + m [MOD m + 1] by exact Nat.ModEq.add_right_cancel' m this
    rw [show y - 1 + m * (2 * x + y - 1) + m = y - 1 + m * (2 * x + y - 1 + 1) by ring]
    rw [show 2 * x + y - 1 + 1 = 2 * x + y by omega]
    suffices 2 * c + m + (1 + 2 * x) ≡ y - 1 + m * (2 * x + y) + (1 + 2 * x) [MOD m + 1] by exact Nat.ModEq.add_right_cancel' (1 + 2 * x) this
    rw [show y - 1 + m * (2 * x + y) + (1 + 2 * x) = y + m * (2 * x + y) + 2 * x by omega]
    rw [show y + m * (2 * x + y) + 2 * x = (m + 1) * (2 * x + y) by ring]

    -- Show (m+1)*(2*x+y) ≡ 0 (mod m+1)
    have g3 : (m + 1) * (2 * x + y) ≡ 0 [MOD (m + 1)]:= by
      suffices m + 1 ∣ (m + 1) * (2 * x + y) by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    suffices 2 * c + m + (1 + 2 * x) ≡ 0 [MOD (m + 1)] by exact Nat.ModEq.symm (Nat.ModEq.trans g3 (id (Nat.ModEq.symm this)))

    -- Show m+1 divides m*(m+1)
    have g4 : m + 1 ∣ m * (m + 1):= by simp
    replace hc : c * (m - 2) ≡ 1 [MOD (m + 1)]:= by exact Nat.ModEq.of_mul_left m hc
    replace hc : c * (m - 2) + c * 3 ≡ 1 + c * 3 [MOD (m + 1)]:= by exact Nat.ModEq.add_right (c * 3) hc
    rw [show c * (m - 2) + c * 3 = c * (m - 2 + 3) by ring] at hc
    rw [show m - 2 + 3 = m + 1 by omega] at hc
    rw [show 2 * c + m + (1 + 2 * x) = 2 * c + 2 * x + (m + 1) by ring]

    -- Show m+1 ≡ 0 (mod m+1)
    have g5 : m + 1 ≡ 0 [MOD (m + 1)]:= by
      suffices m + 1 ∣ m + 1 by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    replace g5 : 2 * c + 2 * x + (m + 1) ≡  2 * c + 2 * x + 0 [MOD (m + 1)]:= by exact Nat.ModEq.add_left (2 * c + 2 * x) g5
    rw [show 2 * c + 2 * x + 0 = 2 * c + 2 * x by ring] at g5
    suffices 2 * c + 2 * x ≡ 0 [MOD (m + 1)] by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm this)) (id (Nat.ModEq.symm g5)))
    clear g4 g5

    -- Prove 3 and m+1 are coprime
    have h5 : Nat.Coprime 3 (m + 1):= by
      have g : Nat.Prime 3:= by decide
      by_contra H
      replace H : 3 ∣ m + 1:= by exact (Nat.Prime.dvd_iff_not_coprime g).mpr H
      replace h3 : m + 1 ∣ x * 3 - 1:= by
        replace hx1 : x * 3 ≥ 1:= by omega
        exact (Nat.modEq_iff_dvd' hx1).mp (id (Nat.ModEq.symm h3))
      replace H : 3 ∣ x * 3 - 1:= by exact Nat.dvd_trans H h3
      replace H : 3 ∣ x * 3 - 1 + 3:= by exact Nat.dvd_add_self_right.mpr H
      rw [show x * 3 - 1 + 3 = x * 3 + 2 by omega] at H
      have g : 3 ∣ x * 3:= by simp
      replace H : 3 ∣ 2:= by exact (Nat.dvd_add_iff_right g).mpr H
      omega

    -- Continue with modular arithmetic manipulations
    replace h3 : x * 3 + c * 3 ≡ 1 + c * 3 [MOD (m + 1)]:= by exact Nat.ModEq.add_right (c * 3) h3
    replace h3 : x * 3 + c * 3 ≡ c * (m + 1) [MOD (m + 1)]:= by exact Nat.ModEq.symm (Nat.ModEq.trans hc (id (Nat.ModEq.symm h3)))
    have g4 : c * (m + 1) ≡ 0 [MOD (m + 1)]:= by
      suffices m + 1 ∣ c * (m + 1) by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    replace h3 : x * 3 + c * 3 ≡ 0 [MOD (m + 1)]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm g4)) (id (Nat.ModEq.symm h3)))
    replace h3 : m + 1 ∣ x * 3 + c * 3:= by exact Nat.dvd_of_mod_eq_zero h3
    rw [show x * 3 + c * 3 = 3 * (x + c) by ring] at h3
    replace h5 : Nat.Coprime (m + 1) 3:= by exact Nat.coprime_comm.mp h5
    replace h3 : m + 1 ∣ x + c:= by exact Nat.Coprime.dvd_of_dvd_mul_left h5 h3
    suffices m + 1 ∣ 2 * c + 2 * x by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat this)
    rw [show 2 * c + 2 * x = 2 * (x + c) by ring]
    exact Dvd.dvd.mul_left h3 2

  -- Prove second part: congruence modulo m
  have g2 : (2 * c + (m + 1) * d) % m = (y - 1 + m * ((2 * x + y - 1) % (m + 1))) % m:= by
    have g2 : m * ((2 * x + y - 1) % (m + 1)) ≡ 0 [MOD m]:= by
      suffices m ∣ m * ((2 * x + y - 1) % (m + 1)) by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    replace g2 : y - 1 + m * ((2 * x + y - 1) % (m + 1)) ≡ y - 1 + 0 [MOD m]:= by exact Nat.ModEq.add_left (y - 1) g2
    simp at g2
    rw [g2]
    suffices 2 * c + (m + 1) * d ≡ y - 1[MOD m] by exact this
    clear g2

    -- Show m+1 ≡ 1 (mod m)
    have g2 : m + 1 ≡ 1 [MOD m]:= by simp
    replace g2 : (m + 1) * d ≡ 1 * d [MOD m]:= by exact Nat.ModEq.mul g2 rfl
    simp at g2
    replace g2 : 2 * c + (m + 1) * d ≡ 2 * c + d [MOD m]:= by exact Nat.ModEq.add_left (2 * c) g2
    suffices 2 * c + d ≡ y - 1 [MOD m] by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm this)) (id (Nat.ModEq.symm g2)))

    -- Show m divides m*(m+1)
    replace hc : c * (m - 2) ≡ 1 [MOD m]:= by exact Nat.ModEq.of_mul_right (m + 1) hc
    replace hd : d * (m + 4) ≡ 1 [MOD m]:= by exact Nat.ModEq.of_mul_right (m + 1) hd
    replace hc : c * (m - 2) + c * 2 ≡ 1 + c * 2 [MOD m]:= by exact Nat.ModEq.add_right (c * 2) hc
    rw [show c * (m - 2) + c * 2 = c * (m - 2 + 2) by ring] at hc
    rw [show m - 2 + 2 = m by omega] at hc
    rw [show d * (m + 4) = d * m + 4 * d by ring] at hd

    -- Show c*m ≡ 0 (mod m)
    replace g3 : c * m ≡ 0 [MOD m]:= by
      suffices m ∣ c * m by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    replace hc : 1 + c * 2 ≡ 0 [MOD m]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm g3)) hc)

    -- Show d*m ≡ 0 (mod m)
    have g4 : d * m ≡ 0 [MOD m]:= by
      suffices m ∣ d * m by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    replace g4 : d * m + 4 * d ≡ 0 + 4 * d [MOD m]:= by exact Nat.ModEq.add_right (4 * d) g4
    simp at g4
    replace hd : 4 * d ≡ 1 [MOD m]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm g4)) hd
    clear g3 g4

    -- Show m and 2 are coprime
    have g3 : Nat.Coprime m 2:= by exact Nat.coprime_two_right.mpr h1
    replace g3 : Nat.Coprime m (2 ^ 2):= by exact Nat.Coprime.pow_right 2 g3
    simp at g3
    suffices (2 * c + d) * 4 ≡ (y - 1) * 4 [MOD m] by exact Nat.ModEq.symm (Nat.ModEq.cancel_right_of_coprime g3 (id (Nat.ModEq.symm this)))
    suffices (2 * c + d) * 4 + 4 ≡ (y - 1) * 4 + 4 [MOD m] by exact Nat.ModEq.add_right_cancel' 4 this
    rw [show (y - 1) * 4 + 4 = y * 4 by omega]
    rw [show (2 * c + d) * 4 + 4 = 4 * (1 + c * 2) + 4 * d by omega]
    replace hd : 4 * d ≡ y * 4 [MOD m]:= by exact Nat.ModEq.trans hd (id (Nat.ModEq.symm h4))
    replace hc : 4 * (1 + c * 2) ≡ 4 * 0 [MOD m]:= by exact Nat.ModEq.mul rfl hc
    replace hc:= Nat.ModEq.add hc hd
    simp at hc
    exact hc

  -- Prove m and m+1 are coprime
  have g3 : Nat.Coprime m (m + 1):= by
    suffices Nat.Coprime m 1 by exact Nat.coprime_self_add_right.mpr this
    simp

  -- Define variables for cleaner notation
  set A:= 2 * c + (m + 1) * d with hA
  set B:= y - 1 + m * ((2 * x + y - 1) % (m + 1)) with hB
  clear_value A B

  -- Show B < m*(m+1)
  have g4 : B < m * (m + 1):= by
    subst B
    have g4 : (2 * x + y - 1) % (m + 1) < m + 1:= by refine Nat.mod_lt (2 * x + y - 1) (by omega)
    replace g4 : (2 * x + y - 1) % (m + 1) ≤ m:= by omega
    replace g4 : m * ((2 * x + y - 1) % (m + 1)) ≤ m * m:= by exact Nat.mul_le_mul_left m g4
    replace hy : y - 1 < m:= by omega
    linarith

  -- Final steps using Chinese Remainder Theorem
  suffices A % (m * (m + 1)) = B % (m * (m + 1)) by rw [this] ; exact Nat.mod_eq_of_lt g4
  clear g4
  by_cases hAB : A ≥ B
  .
    -- Case A ≥ B
    replace g1 : m + 1 ∣ A - B:= by exact (Nat.modEq_iff_dvd' hAB).mp (id (Eq.symm g1))
    replace g2 : m ∣ A - B:= by exact (Nat.modEq_iff_dvd' hAB).mp (id (Eq.symm g2))
    have g4 : m * (m + 1) ∣ A - B:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd g3 g2 g1
    replace g4 : A - B ≡ 0 [MOD m * (m + 1)]:= by exact Nat.modEq_zero_iff_dvd.mpr g4
    replace g4 : A - B + B ≡ 0 + B [MOD m * (m + 1)]:= by exact Nat.ModEq.add_right B g4
    rw [show A - B + B = A by omega] at g4
    simp at g4
    exact g4
  .
    -- Case A < B
    replace hAB : B ≥ A:= by omega
    replace g1 : m + 1 ∣ B - A:= by exact (Nat.modEq_iff_dvd' hAB).mp g1
    replace g2 : m ∣ B - A:= by exact (Nat.modEq_iff_dvd' hAB).mp g2
    have g4 : m * (m + 1) ∣ B - A:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd g3 g2 g1
    replace g4 : B - A ≡ 0 [MOD m * (m + 1)]:= by exact Nat.modEq_zero_iff_dvd.mpr g4
    replace g4 : B - A + A ≡ 0 + A [MOD m * (m + 1)]:= by exact Nat.ModEq.add_right A g4
    rw [show B - A + A = B by omega] at g4
    simp at g4
    rw [g4]
