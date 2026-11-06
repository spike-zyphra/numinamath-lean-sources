import Mathlib
/- Trouver tous les entiers strictement positifs $m$ et $n$ tels que

$$
3 \cdot 2^{\mathrm{m}}+1=\mathrm{n}^{2} .
$$ -/

theorem number_theory_607565 : {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ 3 * 2 ^ m + 1 = n ^ 2} = {(4, 7), (3, 5)}:= by
    -- We use extensionality to prove equality of sets by showing each element belongs to both or neither
    ext ⟨m, n⟩
    constructor
    -- First direction: if (m,n) satisfies the equation, then it must be one of our two solutions
    .
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3⟩
        -- We split into cases based on whether n is even or odd
        by_cases hn : Even n
        -- Case 1: n is even
        .
            -- We prove that if n is even, then m must be 0, which contradicts m > 0
            have h4 : m = 0:= by
                replace hn : Even (n ^ 2):= by refine (Nat.even_pow' (by omega)).mpr hn
                by_contra H
                have h5 : Even 2:= by decide
                replace h5 : Even (2 ^ m):= by exact (Nat.even_pow' H).mpr h5
                replace h5 : Even (3 * 2 ^ m):= by exact Even.mul_left h5 3
                replace h5 : Odd (3 * 2 ^ m + 1):= by exact Even.add_one h5
                rw [h3] at h5
                absurd hn
                simp
                exact h5
            linarith
        -- Case 2: n is odd
        .
            simp at hn
            -- We set t = n - 1, so n = t + 1
            set t:= n - 1 with ht
            clear_value t
            replace ht : n = t + 1:= by omega
            subst n
            -- We prove that t must be even
            replace hn : Even t:= by
                by_contra H
                simp at H
                have h4 : Odd 1:= by decide
                replace H : Even (t + 1):= by exact Odd.add_odd H h4
                absurd hn
                simp
                exact H
            -- Rewriting the equation in terms of t
            replace h3 : 3 * 2 ^ m = t * (t + 2):= by linarith
            replace hn : ∃ s : ℕ, t = s + s:= by exact hn
            rcases hn with ⟨s, hs⟩
            ring_nf at hs
            subst t
            -- Further simplification of the equation
            rw [show s * 2 * (s * 2 + 2) = 4 * s * (s + 1) by ring] at h3
            -- We prove that m ≥ 2
            replace h1 : m ≥ 2:= by
                by_contra H
                simp at H
                replace H : m = 1:= by omega
                subst m
                simp at h3
                replace h3 : 4 ∣ 6:= by rw [h3] ; rw [show 4 * s * (s + 1) = 4 * (s * (s + 1)) by ring] ; simp
                omega
            -- We set r = m - 2, so m = r + 2
            set r:= m - 2 with hr
            clear_value r
            replace hr : m = r + 2:= by omega
            subst m
            rw [show 3 * 2 ^ (r + 2) = 3 * 2 ^ r * 4 by ring] at h3
            -- Simplifying the equation further
            replace h3 : 3 * 2 ^ r = s * (s + 1):= by linarith
            clear h1
            -- We split into cases based on whether s is odd or even
            by_cases hs : Odd s
            -- Case 2.1: s is odd
            .
                replace hs : Nat.Coprime 2 s:= by exact Nat.coprime_two_left.mpr hs
                replace hs : Nat.Coprime (2 ^ r) s:= by exact Nat.Coprime.pow_left r hs
                have h1 : 2 ^ r ∣ s * (s + 1):= by rw [←h3] ; simp
                replace h1 : 2 ^ r ∣ s + 1:= by exact Nat.Coprime.dvd_of_dvd_mul_left hs h1
                replace h1 : ∃ e : ℕ, s + 1 = (2 ^ r) * e:= by exact h1
                rcases h1 with ⟨e, he⟩
                rw [he] at h3
                -- Deriving that 3 = s * e
                replace h3 : 3 = s * e:= by
                    zify
                    zify at h3
                    replace h3 : (2 : ℤ) ^ r * (3 - s * e) = 0:= by linarith
                    simp at h3
                    linarith
                -- Since 3 is prime and s divides 3, s must be 1 or 3
                have h1 : s ∣ 3:= by rw [h3] ; simp
                have g1 : Nat.Prime 3:= by norm_num
                replace h1 : s = 1 ∨ s = 3:= by exact (Nat.dvd_prime g1).mp h1
                rcases h1 with h1 | h1
                -- Subcase: s = 1
                .
                    subst s
                    simp at h3
                    rw [←h3] at he
                    simp at he
                    omega
                -- Subcase: s = 3
                .
                    subst s
                    simp at h3
                    subst e
                    simp at he
                    rw [show 4 = 2 ^ 2 by norm_num] at he
                    replace he : Nat.log 2 (2 ^ 2) = Nat.log 2 (2 ^ r):= by rw [he]
                    repeat rw [Nat.log_pow (by omega)] at he
                    rw [←he]
                    simp
            -- Case 2.2: s is even
            .
                simp at hs
                have g1 : Odd 1:= by decide
                replace hs : Odd (s + 1):= by exact Even.add_one hs
                clear g1
                replace hs : Nat.Coprime 2 (s + 1):= by exact Nat.coprime_two_left.mpr hs
                replace hs : Nat.Coprime (2 ^ r) (s + 1):= by exact Nat.Coprime.pow_left r hs
                have h1 : 2 ^ r ∣ s * (s + 1):= by rw [←h3] ; simp
                replace h1 : 2 ^ r ∣ s:= by exact Nat.Coprime.dvd_of_dvd_mul_right hs h1
                replace h1 : ∃ e : ℕ, s = (2 ^ r) * e:= by exact h1
                rcases h1 with ⟨e, he⟩
                rw [show s * (s + 1) = 2 ^ r * e * (s + 1) by rw [he]] at h3
                -- Deriving that 3 = e * (s + 1)
                replace h3 : 3 = e * (s + 1):= by
                    zify
                    zify at h3
                    replace h3 : (2 : ℤ) ^ r * (3 - e * (s + 1)) = 0:= by linarith
                    simp at h3
                    linarith
                -- Since 3 is prime and s+1 divides 3, s+1 must be 1 or 3
                have h4 : s + 1 ∣ 3:= by rw [h3] ; simp
                have g1 : Nat.Prime 3:= by norm_num
                replace h4 : s + 1 = 1 ∨ s + 1 = 3:= by exact (Nat.dvd_prime g1).mp h4
                rcases h4 with h4 | h4
                -- Subcase: s + 1 = 1, which means s = 0
                .
                    simp at h4
                    rw [h4] at he h3
                    simp at he
                    subst e
                    simp at h3
                -- Subcase: s + 1 = 3, which means s = 2
                .
                    simp at h4
                    rw [h4] at he h3
                    simp at h3
                    subst e
                    simp at he
                    replace he : Nat.log 2 (2 ^ r) = Nat.log 2 2:= by rw [←he]
                    rw [show Nat.log 2 2 = Nat.log 2 (2 ^ 1) by simp] at he
                    repeat rw [Nat.log_pow (by omega)] at he
                    subst r s
                    simp
    -- Second direction: proving that (4,7) and (3,5) are indeed solutions to the equation
    .
        intro h
        simp at h
        rcases h with h | h
        all_goals
            rcases h with ⟨h1, h2⟩
            subst m n
            simp
