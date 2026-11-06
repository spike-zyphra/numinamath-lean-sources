import Mathlib

/- Task 3. Find all triples $(x, n, p)$ of positive integers $x$ and $n$ and prime numbers $p$ for which


$$

x^{3}+3 x+14=2 \cdot p^{n} \text {. }

$$
 -/

theorem number_theory_168383 (x : ℤ)  (n p : ℕ) (hx : 0 < x) (hn : 0 < n) (hp : Nat.Prime p)
    (h : x^3 + 3 * x + 14 = 2 * p^n) :
    (x, n, p) = (1, 2, 3) ∨ (x, n, p) = (3, 2, 5) := by
-- We will need in the proof the "Facts" that p is prime and that 3 and 5 are prime.
      have hpFact : Fact (Nat.Prime p) := ⟨hp⟩
      have h3Fact : Fact (Nat.Prime 3) := by decide
      have h5Fact : Fact (Nat.Prime 5) := by decide
-- We factorize $x^3+3x+14 = (x+2)(x^2-2x+7)$.
      have : x^3 + 3 * x + 14 = (x + 2) * (x^2 - 2 * x + 7) := by
        ring_nf
      rw [this] at h
-- We first assume that $x$ is even. This will yield no solutions.
      by_cases hxeven : Even x
      · exfalso
--It follows that $x+2$ is also even.
        have : Even (x + 2) := by
          rw [Int.even_add]
          simp only [even_two, iff_true, hxeven]
--Since $x+2$ is even and divides $2*p^n$, it must be of the form $2*p^a$ for some $a≤n$.
        have : ∃ a : ℕ, (a ≤ n) ∧ x + 2 = 2 * p ^ a := by
          rw [even_iff_two_dvd] at this
          obtain ⟨k,hk⟩ := this
          suffices ∃ a : ℕ , (a ≤ n) ∧ k = p^a by
            obtain ⟨a,ha⟩ := this
            use a
            rw [hk, ← ha.2]
            simp only [and_true, ha.1]
          have knezero : k ≠ 0 := by
            intro h
            linarith
          rw [hk, mul_assoc] at h
          simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at h
          have : k ∣ p ^ n := by
            rw [dvd_def]
            use (x ^ 2 - 2 * x + 7)
            rw [← h]
          rw [dvd_prime_pow (Nat.prime_iff_prime_int.mp hp)] at this
          obtain ⟨a,h1,h2⟩ := this
          use a
          rw [Associated] at h2
          rcases h2 with ⟨u,h2⟩
          have u1 := Int.units_eq_one_or u
          have upos : u.val > 0 := by
            have mulpos : k * u.val > 0 := by
              rw [h2]
              apply pow_pos
              exact_mod_cast Nat.Prime.pos hp
            have : k > 0 := by linarith
            simp_rw [mul_pos_iff] at mulpos
            rcases mulpos with ⟨hkpos,hupos⟩
            · exact hupos
            · linarith
          have : u.val = 1 := by
            by_cases hu : u = 1
            · rw [hu]
              simp only [Units.val_one]
            · exfalso
              have : u.val = -1 := by
                rw [or_iff_not_imp_left] at u1
                have := u1 hu
                simp only [this, Units.val_neg, Units.val_one, Int.reduceNeg]
              linarith
          rw [this, mul_one] at h2
          exact ⟨h1,h2⟩
        obtain ⟨a,ha⟩ := this
-- We observe that $a>0$, since $x>0$, thus $x+2>2$, and $a=0$ would give a contradiction.
        have apos : a > 0 := by
          by_contra hapos
          simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at hapos
          rw [hapos] at ha
          simp only [pow_zero, mul_one, add_left_eq_self] at ha
          linarith
--We now simplify the equation, obtaining $x^2-2x+7 = p^{n-a}$.
        have hna : x ^ 2 - 2 * x + 7 = p ^ (n - a) := by
          rw [ha.2] at h
          have : 2 * p ^ a * p ^ (n - a) = 2 * p ^ n := by
            rw [mul_assoc, ← pow_add, (by omega : a + (n - a) = n)]
          rw_mod_cast [← this] at h
          simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_eq_mul_left_iff, mul_eq_zero,
            OfNat.ofNat_ne_zero, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq, false_or] at h
          cases h
          · simp only [Nat.cast_pow]; assumption
          · exfalso; apply Nat.Prime.ne_zero hp; omega
--We observe that $x^2-2x+7>x+2$, thus $n-a>a$.
        have : x ^ 2 - 2 * x + 7 > x + 2 := by
          suffices x ^ 2 - 3 * x + 5 > 0 by
            linarith
          have : (x ^ 2 - 3 * x + 5 : ℚ)  > (x - 3/2) ^ 2 := by
            ring_nf
            simp only [gt_iff_lt, add_lt_add_iff_right, sub_lt_sub_iff_right]
            linarith
          qify
          apply lt_of_le_of_lt _ this
          positivity
        have hnagta: n - a > a := by
          rw [ha.2, hna] at this
          have : (p : ℤ) ^ (n-a) > p ^ a := by
            apply lt_trans (by linarith : (p : ℤ) ^ a < 2 * p ^ a) this
          rw [gt_iff_lt, pow_lt_pow_iff_right₀ ] at this
          exact this
          exact_mod_cast Nat.Prime.one_lt hp
--From $x+2=2p^a$, we deduce an expression from x$, which we substitute in the second equation.
        have hx : x = 2 * p ^ a - 2 := by
          rw [ha.2] at h
          linarith
        rw [hx] at h
        ring_nf at h
        have : p ^ n * 2 = p ^ (n - a) * (2 * p ^ a) := by
          rw [mul_comm 2, ← mul_assoc, ← pow_add, (by omega : n - a + a = n)]
        zify at this
        rw [this] at h
-- We simplify the equation to get $15 = p^a*12 - p^{2a}*4 + p^{n-a}$.
        have : (p ^ a * 30 - p ^ (a * 2) * 24 + p ^ (a * 3) * 8 : ℤ) = (15 - p ^ a * 12 + p ^ (2 * a) * 4) * (2 * p ^ a) := by
          ring_nf
        rw [this] at h
        simp only [mul_eq_mul_right_iff, mul_eq_zero, OfNat.ofNat_ne_zero, pow_eq_zero_iff',
          Nat.cast_eq_zero, ne_eq, false_or] at h
        have : (p = 0 ∧ ¬a = 0) = False := by
          have : (p = 0) = False := by
            simp only [eq_iff_iff, iff_false]
            exact Nat.Prime.ne_zero hp
          simp only [this, false_and]
        rw [this] at h
        rw [or_false] at h
        have h15 : 15 = (p : ℤ) ^ a * 12 - p ^ (2 * a) * 4 + p ^ (n - a) := by
          linarith
-- From $n-a>a$, we know $p^a∣p^{n-a}$.
        have : p ^ a ∣ p ^ (n - a) := by
          apply pow_dvd_pow
          exact le_of_lt hnagta
-- We obtain that $p^a|15$.
        have pdiv15 : (p : ℤ) ^ a ∣ (p : ℤ) ^ a * 12 - p ^ (2 * a) * 4 + p ^ (n - a) := by
          apply Dvd.dvd.add
          · use (12 - p ^ a * 4)
            ring_nf
          · exact_mod_cast this
        rw [← h15] at pdiv15
-- This yields that $p=3$ or $p=5$ and $a=1$.
        have : (p = 3 ∨ p = 5) ∧ a = 1 := by
          rw_mod_cast [Nat.Prime.pow_dvd_iff_dvd_ordProj hp (by linarith)] at pdiv15
          rw [Nat.factorization_def] at pdiv15
          rw [pow_dvd_pow_iff (Nat.Prime.ne_zero hp) _] at pdiv15
          · rw [(by linarith : 15 = 3 * 5), (padicValNat.mul (by linarith) (by linarith))] at pdiv15
            by_cases hp : p = 3 ∨ p = 5
            · by_cases h3 : p = 3
              · rw [h3, padicValNat_self, padicValNat_primes (by linarith)] at pdiv15
                exact ⟨hp,(by linarith)⟩
              · have h5 : p = 5 := by
                  tauto
                rw [h5, padicValNat_self, padicValNat_primes (by linarith)] at pdiv15
                exact ⟨hp,(by linarith)⟩
            · exfalso
              push_neg at hp
              rw [padicValNat_primes (hp.1), padicValNat_primes (hp.2)] at pdiv15
              linarith
          · exact_mod_cast Prime.not_unit (Nat.prime_iff_prime_int.mp hp)
          · exact hp
        obtain ⟨hp,ha⟩ := this
--We subsitute the values of $p$ and $a$ in the equations for $x$ and we obtain contradictions.
        rw [ha, pow_one] at hx
        rw [ha, hx] at hna
        rw [ha] at h15
        ring_nf at h15
        by_cases hp3 : p = 3
-- If $p=3$, we obtain that 15 is equal to a power of 3, a contradiction.
        · rw [hp3] at h15
          ring_nf at h15
          rw [(by linarith : (15 : ℤ) = 3 * 5)] at h15
          have : (3 : ℤ) ^ (n - 1) = 3 * 3 ^ (n - 2) := by
            nth_rw 2 [← pow_one 3]
            rw [← pow_add, (by omega : 1 + (n - 2) = n - 1)]
          rw [this] at h15
          rw [mul_eq_mul_left_iff] at h15
          simp at h15
          symm at h15
          rw_mod_cast [Nat.Prime.pow_eq_iff] at h15
          · linarith
          · decide
-- If $p=5$, we obtain that 15 is equal to a power of 5, again a contradiction.
        · have hp5 : p = 5 := by
            tauto
          rw [hp5] at h15
          ring_nf at h15
          have : ∀ a b c : ℤ, a = -b+c ↔ a+b = c := by
            intro a b c
            constructor
            · intro h
              linarith
            · intro h
              linarith
          rw [this] at h15
          rw [(by linarith : (15 : ℤ) + 40 = 55)] at h15
          rw [(by linarith : (55 : ℤ) = 5 * 11)] at h15
          have : (5 : ℤ) ^ (n - 1) = 5 * 5 ^ (n - 2) := by
            nth_rw 2 [← pow_one 5]
            rw [← pow_add, (by omega : 1 + (n - 2) = n - 1)]
          rw [this] at h15
          rw [mul_eq_mul_left_iff] at h15
          simp at h15
          symm at h15
          rw_mod_cast [Nat.Prime.pow_eq_iff] at h15
          · linarith
          · decide
-- We now move to the case where $x$ is odd.
      · have hxodd : ∃ a : ℕ, a ≤ n ∧ x + 2 = p ^ a := by
          have : (x + 2) ∣ 2 * p ^ n := by
            use (x ^ 2 - 2 * x + 7)
            rw [h]
-- In this case, $x+2$ is also odd.
          have hx2odd : ¬ Even (x + 2) := by
            simp only [Int.even_add, even_two, iff_true, Int.not_even_iff_odd]
            simp only [Int.not_even_iff_odd] at hxeven
            exact hxeven
-- Since $x+2$ is odd and divides $2*p^n$, it must be of the form $p^a$ for some $a≤n$.
          have : x + 2 ∣ p ^ n := by
            obtain ⟨k,hk⟩ := this
            have : Even k := by
              have : 2 ∣ (x + 2) * k := by
                use p ^ n
                rw [hk]
              rw [Prime.dvd_mul (by apply Nat.prime_iff_prime_int.mp; decide)] at this
              rw [or_iff_not_imp_left] at this
              rw [even_iff_two_dvd] at *
              have := this hx2odd
              exact this
            obtain ⟨k2,hk2⟩ := this
            use k2; ring_nf at hk2
            rw [hk2] at hk
            linarith
          rw [dvd_prime_pow (Nat.prime_iff_prime_int.mp hp)] at this
          obtain ⟨a,h1,h2⟩ := this
          use a
          constructor
          · exact h1
          · rw [Associated] at h2
            rcases h2 with ⟨u,h2⟩
            have u1 := Int.units_eq_one_or u
            by_cases hu : u = 1
            · rw_mod_cast [hu, mul_one] at h2
              exact_mod_cast h2
            · exfalso
              have : u.val = -1 := by
                rw [or_iff_not_imp_left] at u1
                have := u1 hu
                simp only [this, Units.val_neg, Units.val_one, Int.reduceNeg]
              rw [this] at h2
              have : x + 2 > 0 := by
                linarith
              have : p ^ a > 0 := by
                apply pow_pos
                exact_mod_cast Nat.Prime.pos hp
              linarith
        obtain ⟨a,halen,hpa⟩ := hxodd
-- We simplify the equation to get $x^2-2x+7 = p^{n-a}$.
        rw [hpa] at h
        have h2 : x ^ 2 - 2 * x + 7 = 2 * p ^ (n - a) := by
          have : p ^ n = p ^ (n - a) * p ^ a := by
            rw [← pow_add, (by omega : n - a + a = n)]
          rw_mod_cast [this] at h
          rw [mul_comm, ← mul_assoc] at h
          simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_eq_mul_right_iff,
            pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq] at h
          cases h
          · simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
            assumption
          · exfalso
            apply Nat.Prime.ne_zero hp
            omega
-- We now have an expression for $x$, namely $x=p^a-2$, that we substitute in the second equation.
        have : x = p ^ a  - 2 := by
          rw [← hpa] at h
          linarith
        have h15 : ((p : ℤ) ^ a - 2) ^ 2 - 2 * (p ^ a - 2) + 7 = 2 * p ^ (n - a) := by
          rw [← this]
          exact h2
        ring_nf at h15
-- We observe that $a > 0$, since if not we would have a contradiction with the fact that $x + 2$ is positive and odd.
        have ha : a > 0 := by
          by_contra hapos
          simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at hapos
          rw [hapos] at hpa
          simp only [pow_zero, mul_one, add_left_eq_self] at hpa
          linarith
-- We manipulate the equations to get $x ^ 2 - 2 * x + 7 ≥ 2 * (x + 2)$, thus, in particular, $n-a ≥ a$.
        have hpoly : x ^ 2 - 4 * x + 3 ≥ 0 := by
          have : 0 < (x - 2)^2 := by
            rw [LE.le.gt_iff_ne]
            · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
              intro x2
              rw [sub_eq_zero] at x2
              rw [x2] at hxeven
              contradiction
            · positivity
          suffices x ^ 2 - 4 * x + 3 = (x - 2)^2 - 1 by
            rw [this]
            linarith
          ring_nf
        have : x ^ 2 - 2 * x + 7 ≥ 2 * (x + 2) := by
          rw [(by linarith : x ^ 2 - 2 * x + 7 = x ^ 2 - 4 * x + 3 + 2 * x + 4)]
          linarith
        simp only [hpa, h2, ge_iff_le, Nat.ofNat_pos, mul_le_mul_left] at this
        have : a ≤ n - a := by
          rw [pow_le_pow_iff_right₀] at this
          · exact this
          · exact_mod_cast Nat.Prime.one_lt hp
-- We now have an expression for 15 that is divisible by $p^a$.
        have h15' : 15 = (p : ℤ) ^ a * 6 - p ^ (a * 2) + p ^ (n - a) * 2 := by
          linarith
        have : (p : ℤ) ^ a ∣ (p : ℤ) ^ a * 6 - p ^ (a * 2) + p ^ (n - a) * 2 := by
          apply Dvd.dvd.add
          · use (6 - p ^ a)
            ring_nf
          · use (p ^ (n - 2 * a) * 2)
            rw [← mul_assoc, ← pow_add, (by omega : a + (n - 2 * a) = n - a)]
        rw [← h15'] at this
-- Since $p^a$ divides 15, we have $p=3$ or $p=5$ and $a=1$.
        have : (p = 3 ∨ p = 5) ∧ a = 1 := by
          rw_mod_cast [Nat.Prime.pow_dvd_iff_dvd_ordProj hp (by linarith)] at this
          rw [Nat.factorization_def] at this
          rw [pow_dvd_pow_iff (Nat.Prime.ne_zero hp) _] at this
          · rw [(by linarith : 15 = 3 * 5), (padicValNat.mul (by linarith) (by linarith))] at this
            by_cases hp : p = 3 ∨ p = 5
            · by_cases h3 : p = 3
              · rw [h3, padicValNat_self, padicValNat_primes (by linarith)] at this
                exact ⟨hp,(by linarith)⟩
              · have h5 : p = 5 := by
                  tauto
                rw [h5, padicValNat_self, padicValNat_primes (by linarith)] at this
                exact ⟨hp,(by linarith)⟩
            · exfalso
              push_neg at hp
              rw [padicValNat_primes (hp.1), padicValNat_primes (hp.2)] at this
              linarith
          · exact_mod_cast Prime.not_unit (Nat.prime_iff_prime_int.mp hp)
          · exact hp
        obtain ⟨hp,ha⟩ := this
-- We rewrite $a=1$ in the equations for $x$.
        rw [ha, pow_one] at h
        rw [ha, pow_one] at hpa
        by_cases hp3 : p = 3
-- We consider the case where $p=3$. Solving yields $x=1$ and $n=2$.
        · rw [hp3] at hpa
          zify at hpa
          have x1 : x = 1 := by linarith
          rw [x1, hp3] at h
          simp only [Nat.cast_ofNat, one_pow, mul_one, Int.reduceSub, Int.reduceAdd,
            Int.reduceMul] at h
          have n2 : n = 2 := by
            have : (9 : ℤ) = (3 : ℤ) ^ n := by
              rw [(by linarith : (18 : ℤ) = 2 * 9)] at h
              qify
              apply mul_left_cancel₀ (by linarith : (2 : ℚ) ≠ 0)
              exact_mod_cast h
            rw [(by linarith : (9 : ℤ) = 3 ^ 2)] at this
            rw [pow_right_inj₀ (by linarith) (by linarith)] at this
            rw [this]
          left
          rw [x1, n2, hp3]
-- We consider the case where $p=5$. Solving yields $x=3$ and $n=2$.
        · have hp5 : p = 5 := by tauto
          rw [hp5] at hpa
          zify at hpa
          have x3 : x = 3 := by linarith
          rw [x3, hp5] at h
          simp only [Nat.cast_ofNat, one_pow, mul_one, Int.reduceSub, Int.reduceAdd,
            Int.reduceMul] at h
          have n2 : n = 2 := by
            have : (25 : ℤ) = (5 : ℤ) ^ n := by
              norm_num at h
              rw [(by linarith : (50 : ℤ) = 2 * 25)] at h
              qify
              apply mul_left_cancel₀ (by linarith : (2 : ℚ) ≠ 0)
              exact_mod_cast h
            rw [(by linarith : (25 : ℤ) = 5 ^ 2)] at this
            rw [pow_right_inj₀ (by linarith) (by linarith)] at this
            rw [this]
          right
          rw [x3, n2, hp5]