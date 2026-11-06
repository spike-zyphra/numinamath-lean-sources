import Mathlib

/- Soit $n>0$ un entier, et $a, b, c$ des entiers strictement positifs tels que

$$
(a+b c)(b+a c)=19^{n}
$$

Prouver que n est pair. -/
theorem number_theory_604634 {n : ℕ} (hn : n > 0) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : (a + b * c) * (b + a * c) = 19 ^ n) :
    Even n := by

  -- We consider two cases depending on whether $c = 1 \or a = b$ or not.
  by_cases hcab : c = 1 ∨ a = b
  . -- First, consider the case when $c = 1$ or $a = b$.
    -- We show that if $p ^ n$ equals to the square of another
    -- natural number where $p$ is prime, then $n$ is even.
    have h1 {a p n : ℕ} (hp : Nat.Prime p) (h : a ^ 2 = p ^ n) : Even n := by
      have : n = (a ^ 2).factorization p := by
        simp [h, Nat.factorization_pow]
        have : p.factorization p = 1 := by exact Nat.Prime.factorization_self hp
        rw [this, mul_one]
      simp at this
      rw [this]
      exact even_two_mul (a.factorization p)

    -- Whether $c = 1$ or $a = b$, the left-hand side of the equation
    -- $(a + bc)(b + ac) = 19^{n}$ reduces to the square of a natural number.
    -- Thus, by the result above, $n$ is even since $19$ is prime.
    obtain g | g := hcab
    repeat
    . simp [g, add_comm, ← pow_two] at h
      apply (h1 (by decide) h)

  . -- Now, consider the case when $c = 1$ or $a = b$ is not true.
    simp at hcab

    -- Then, $c \neq 1$ and $a \neq b$.
    obtain ⟨ hc1, hab ⟩ := hcab

    -- The left-hand side of the equation $(a + bc)(b + ac) = 19^{n}$ is
    -- symmetric in $a$ and $b$. Since $a \neq b$, we assume without
    -- loss of generality that $a > b$.
    wlog H: a > b
    . obtain g := this hn b a c hb ha hc
      apply g
      . rw [← h]; ring
      . exact hc1
      . intro hba; apply hab; symm; exact hba
      . omega
    . -- Without loss of generality, we may assume that $19$ does not divide $a$.
      wlog G: ¬19 ∣ a with result
      . -- Indeed, if $19$ divides $a$, then let $k$ be the largest
        -- natural number so that $19 ^ k$ divides $a$.
        simp at G
        have : ∃ k, 19 ^ k ∣ a ∧ ¬19 ^ (k + 1) ∣ a := by
          use a.factorization 19
          constructor
          . exact Nat.ordProj_dvd a 19
          . refine Nat.pow_succ_factorization_not_dvd ?_ ?_
            . exact Nat.not_eq_zero_of_lt ha
            . decide
        obtain ⟨ k, ⟨ hkdvd, hkndvd ⟩ ⟩ := this
        -- We can write $a$ as $19^k r$ for some positive natural number r.
        obtain ⟨ r, hr ⟩ := hkdvd
        have hrpos : 0 < r := by rw [hr] at ha; exact Nat.pos_of_mul_pos_left ha

        -- Then, $19 ^ k$ must divide $b + ac$.
        have claim3 : 19 ^ k ∣ b + a * c := by
          have : b + a*c ∣ 19 ^ n := by exact Dvd.intro_left (a + b * c) h
          rw [Nat.dvd_prime_pow (by decide)] at this
          obtain ⟨ k', ⟨ hk'l, hk'r ⟩ ⟩ := this
          have : k' ≥ k := by
            rw [hr] at hk'r
            by_contra h'
            simp at h'
            have : b + 19 ^ k * r  * c > 19 ^ k' := by
              calc
                _ > 19 ^ k * r * c := by exact Nat.lt_add_of_pos_left hb
                _ ≥ 19 ^ k * 1 := by rw [mul_assoc]
                                     refine Nat.mul_le_mul_left (19 ^ k) ?_
                                     nlinarith only [hc, hrpos]
                _ > _ := by rw [mul_one]
                            refine Nat.pow_lt_pow_of_lt ?_ h'
                            norm_num
            simp [hk'r, h'] at this
          rw [hk'r]
          exact Nat.pow_dvd_pow_iff_le_right'.mpr this
        rw [hr, mul_assoc] at claim3

        -- We conclude that $19 ^ k$ also divides $b$.
        rw [← Nat.dvd_add_iff_left (Nat.dvd_mul_right (19 ^ k) _)] at claim3
        obtain ⟨ s, hs ⟩ := claim3
        -- We can write $b$ as $19^k s$ for some positive natural number s.
        have hspos : 0 < s := by rw [hs] at hb; exact Nat.pos_of_mul_pos_left hb

        -- Note that $n - 2k > 0$.
        have claim4 : n - (2 * k) > 0 := by
          rw [hr, hs] at h
          have : (19 ^ k * r + 19 ^ k * s * c) * (19 ^ k * s + 19 ^ k * r * c) =
                 (19 ^ k) * (19 ^ k) * (r + s * c) * (s + r * c) := by ring
          rw [this, ← pow_two, ← pow_mul] at h
          rw [mul_assoc] at h
          have h0 : 19 ^ (k * 2) < 19 ^ n := by
            rw [← h]
            refine (Nat.lt_mul_iff_one_lt_right ?_).mpr ?_
            . exact Nat.pos_of_neZero (19 ^ (k * 2))
            . have h1 : r + s * c > 1 := by
                calc
                  _ ≥ 1 + s * c := by exact Nat.add_le_add_right hrpos (s * c)
                  _ ≥ 1 + 1 := by refine Nat.add_le_add_left ?_ 1; exact Right.one_le_mul hspos hc
                  _ > _ := by norm_num
              have h2 : s + r * c > 1 := by
                calc
                  _ ≥ 1 + r * c := by exact Nat.add_le_add_right hspos (r * c)
                  _ ≥ 1 + 1 := by refine Nat.add_le_add_left ?_ 1; exact Right.one_le_mul hrpos hc
                  _ > _ := by norm_num
              exact Right.one_lt_mul' h1 h2
          rw [mul_comm]
          suffices k * 2 < n by exact Nat.zero_lt_sub_of_lt this
          by_contra g
          simp at g
          have h0' : 19 ^ n ≤ 19 ^ (k * 2) := by refine Nat.pow_le_pow_right ?_ g; norm_num
          linarith

        -- Note that $n$ is even iff $n - 2k$ is even.
        have g : Even n ↔ Even (n - (2 * k)) := by
          refine (Nat.even_sub ?_).mp ?_
          . omega
          . rw [Nat.sub_sub_self (by omega)]; exact even_two_mul k

        -- Hence, it is sufficient to prove that $n - 2k$ is even.
        rw [g]

        -- It follows from the result applied to $(r + sc)(s + rc) = 19^(n - 2k)
        refine result claim4 r s c hrpos hspos hc ?_ hc1 ?_ ?_ ?_
        . rw [hr, hs] at h
          suffices (r + s * c) * (s + r * c) * 19 ^ (2 * k) = 19 ^ (n - 2 * k) * 19 ^ (2 * k) by
            rw [← @Nat.mul_right_cancel_iff (19 ^ (2*k))]
            . exact this
            . apply Nat.pos_of_neZero
          rw [← pow_add, Nat.sub_add_cancel]
          . rw [← h]; ring
          . omega
        . rw [hr, hs] at hab
          by_contra g; apply hab; rw [g]
        . rw [hr, hs] at H
          exact Nat.lt_of_mul_lt_mul_left H
        . by_contra gg
          apply hkndvd
          rw [hr, pow_add, pow_one]
          exact Nat.mul_dvd_mul_left (19 ^ k) gg

      . -- We assume that $19$ does not divide $a$.

        -- Note that $a + bc > 1$.
        have claim0 : a + b * c > 1 := by nlinarith only [ha, hb, hc, H]

        -- Note also that $b + ac > a + bc$.
        have claim1 : b + a * c > a + b * c := by
          have h1 : 0 < a - b := by omega
          have h2 : 0 < c - 1 := by omega
          have h3 : 0 < (a - b) * (c - 1) := Nat.mul_pos h1 h2
          have h4 : c > 1 := by omega
          nlinarith [h3, H, h4]

        -- Then, there exists $u$ such that $a + bc = 19 ^ u$.
        have claim2u : ∃ u, a + b * c = 19 ^ u := by
          have : a + b * c ∣ 19 ^ n := by exact Dvd.intro (b + a * c) h
          rw [Nat.dvd_prime_pow] at this
          . have ⟨ u, hu ⟩ := this
            use u
            omega
          . decide
        obtain ⟨ u, hu ⟩ := claim2u
        -- We see that $u$ must be positive.
        have hupos : u > 0 := by
          by_contra g
          simp at g
          simp [g] at hu
          linarith

        -- We also have that there exists $v$ such that $b + ac = 19 ^ (u+v)$.
        have claim2v : ∃ v, b + a * c = 19 ^ (u + v) := by
          have : b + a * c ∣ 19 ^ n := by exact Dvd.intro_left (a + b * c) h
          rw [Nat.dvd_prime_pow] at this
          . have ⟨ w, hw ⟩ := this
            use (w - u)
            rw [add_comm u, Nat.sub_add_cancel]
            . omega
            . by_contra g
              push_neg at g
              have : u > w := by linarith
              have : 19^u > 19^w := by
                apply Nat.pow_lt_pow_right
                all_goals omega
              linarith
          . decide
        obtain ⟨ v, hv ⟩ := claim2v
        -- Since $b + ac > a + bc$, we have $v > 0$.
        have hvpos : v > 0 := by
          by_contra g
          simp at g
          simp [g] at hv
          linarith

        -- A simple calculation shows that $a(c-1)(c+1) = 19^u(19^v c - 1)$
        have claim3 : a * (c - 1) * (c + 1) = 19 ^ u * (19 ^ v * c - 1) := by
          calc
            _ = a * (c ^ 2 - 1) := by
                  rw [mul_assoc, mul_comm (c-1)]
                  rw [← Nat.sq_sub_sq];
            _ = a * c ^ 2 - a := by exact Nat.mul_sub_one a (c ^ 2)
            _ = 0 + a * c ^ 2 - a := by rw [zero_add]
            _ = (b * c - b * c) + a * c ^ 2 - a := by rw [Nat.sub_self]
            _ = a * c ^ 2 + (b * c - b * c) - a := by rw [add_comm]
            _ = a * c ^ 2 + b * c - b * c - a := by rw [← Nat.add_sub_assoc]; rfl
            _ = (b + a * c) * c - b * c - a := by ring_nf
            _ = (b + a * c) * c - (b * c + a) := by apply Nat.sub_sub
            _ = (b + a * c) * c - (a + b * c) := by rw [add_comm (b * c)]
            _ = _ := by rw [hu, hv, pow_add, Nat.mul_sub, mul_one]
                        ring_nf

        -- By the previous claim, $19 ^ u$ divides $a(c - 1)(c + 1)$.
        -- But $19 ^ u$ and $a$ are coprime since $19$ does not divide $a$.
        -- Thus, $19 ^ u$ divides $(c - 1)(c + 1)$.
        have claim4 : 19 ^ u ∣ (c - 1) * (c + 1) := by
          have h1 : 19 ^ u ∣ a * (c - 1) * (c + 1) := by
            rw [claim3]
            exact Nat.dvd_mul_right (19 ^ u) (19 ^ v * c - 1)
          rw [mul_assoc] at h1
          have h2 : Nat.Coprime (19 ^ u) a := by
            rw [Nat.coprime_comm]
            refine Nat.Prime.coprime_pow_of_not_dvd ?_ G
            decide
          exact Nat.Coprime.dvd_of_dvd_mul_left h2 h1

        -- But the gcd of $c - 1$ and $c + 1$ is either 1 or 2 since
        -- the gcd must divide $(c + 1) - (c - 1) = 2$. Thus, we cannot
        -- have $19$ dividing both $(c - 1)$ and $(c + 1)$.
        -- Thus, we have $19 ^ u$ divides $(c - 1)$ or $19 ^ u$ divides $(c + 1)$.
        have claim5 : 19 ^ u ∣ (c - 1) ∨ 19 ^ u ∣ (c + 1) := by
          by_contra g
          simp at g
          have h1 : 19 ∣ c - 1 := by
            by_contra h0
            have : Nat.Coprime (19 ^ u) (c - 1) := by
              suffices Nat.Coprime 19 (c - 1) by exact Nat.Coprime.pow_left u this
              rw [Nat.Prime.coprime_iff_not_dvd]
              . exact h0
              . decide
            have : 19 ^ u ∣ c + 1 := by exact Nat.Coprime.dvd_of_dvd_mul_left this claim4
            omega
          have h2 : 19 ∣ c + 1 := by
            by_contra h0
            have : Nat.Coprime (19 ^ u) (c + 1) := by
              suffices Nat.Coprime 19 (c + 1) by exact Nat.Coprime.pow_left u this
              rw [Nat.Prime.coprime_iff_not_dvd]
              . exact h0
              . decide
            have : 19 ^ u ∣ c - 1 := by exact Nat.Coprime.dvd_of_dvd_mul_right this claim4
            omega
          have h3 : 19 ∣ (c + 1) - (c - 1) := by exact Nat.dvd_sub' h2 h1
          have h4 : (c + 1) - (c - 1) = 2 := by omega
          rw [h4] at h3
          revert h3
          decide

        -- We arrive at a contradiction.
        by_contra
        revert claim5
        simp
        have h1 : c > 1 := by
          apply Nat.lt_of_le_of_ne hc
          simp; exact fun a => hc1 (id (Eq.symm a))
        constructor
        . suffices 19 ^ u > c - 1 by refine Nat.not_dvd_of_pos_of_lt ?_ this; exact Nat.zero_lt_sub_of_lt h1
          rw [← hu]
          calc
            _ > b + b * c := by exact Nat.add_lt_add_right H (b * c)
            _ = b * (c + 1) := by ring
            _ = b * (c + 1) := by ring
            _ ≥ 1 * (c + 1) := by apply Nat.mul_le_mul_right (c + 1) hb
            _ > c - 1 := by rw [one_mul]; omega
        . suffices 19 ^ u > c + 1 by refine Nat.not_dvd_of_pos_of_lt ?_ this; exact Nat.add_pos_left hc 1
          rw [← hu]
          calc
            _ > b + b * c := by exact Nat.add_lt_add_right H (b * c)
            _ = b * (c + 1) := by ring
            _ = b * (c + 1) := by ring
            _ ≥ 1 * (c + 1) := by apply Nat.mul_le_mul_right (c + 1) hb
            _ = c + 1 := by rw [one_mul]
