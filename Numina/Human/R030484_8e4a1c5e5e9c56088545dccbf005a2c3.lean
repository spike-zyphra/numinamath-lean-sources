import Mathlib
/- Find all ordered pairs of integers $(x, y)$ such that $3^{x} 4^{y}=2^{x+y}+2^{2(x+y)-1}$. -/
theorem algebra_611263 : {(x, y) : ℕ × ℕ | 3 ^ x * 4 ^ y = 2 ^ (x + y) + 2 ^ (2 * (x + y) - 1)} = {(0, 1), (1, 1), (2, 2)}:= by
    -- Use extensionality to prove equality of sets by showing both inclusions
    ext ⟨x, y⟩
    constructor
    .
        -- Forward direction: if (x,y) satisfies the equation, then it's one of the three pairs
        intro h
        simp at h
        -- Prove that x + y > 0
        have h1 : x + y > 0:= by
            by_contra H
            simp at H
            rcases H with ⟨hx, hy⟩
            subst x y
            simp at h
        -- Rewrite the exponent 2*(x+y)-1 as (x+y)-1+(x+y)
        rw [show 2 * (x + y) - 1 = (x + y) - 1 + (x + y) by omega] at h
        -- Apply the power rule: 2^(a+b) = 2^a * 2^b
        rw [show 2 ^ ((x + y) - 1 + (x + y)) = 2 ^ ((x + y) - 1) * 2 ^ (x + y) by ring] at h
        -- Factor out 2^(x+y) from the right side
        rw [show 2 ^ (x + y) + 2 ^ (x + y - 1) * 2 ^ (x + y) = 2 ^ (x + y) * (1 + 2 ^ (x + y - 1)) by ring] at h
        -- Rewrite 4 as 2^2
        rw [show 4 = 2 ^ 2 by ring] at h
        -- Apply the power rule: (a^b)^c = a^(b*c)
        rw [show (2 ^ 2) ^ y = 2 ^ (2 * y) by exact Eq.symm (Nat.pow_mul 2 2 y)] at h
        -- Case analysis: x + y = 1 or x + y > 1
        by_cases h2 : x + y = 1
        .
            -- Handle the case where x + y = 1
            have h3 : x = 1 ∨ x = 0:= by omega
            rcases h3 with h3 | h3
            .
                -- Subcase: x = 1, which implies y = 0
                subst x
                simp at h2
                subst y
                simp at h
            .
                -- Subcase: x = 0, which implies y = 1
                subst x
                simp at h2
                subst y
                simp
        .
            -- Handle the case where x + y > 1
            replace h1 : x + y > 1:= by omega
            clear h2
            -- Prove that 1 + 2^(x+y-1) is coprime to 2
            have h2 : Nat.Coprime (1 + 2 ^ (x + y - 1)) 2:= by
                have h2 : Even 2:= by decide
                replace h2 : Even (2 ^ (x + y - 1)):= by refine (Nat.even_pow' (by omega)).mpr h2
                replace h2 : Odd (1 + 2 ^ (x + y - 1)):= by exact Even.one_add h2
                exact Nat.coprime_two_right.mpr h2
            -- Extend coprimality to 2^(2*y)
            replace h2 : Nat.Coprime (1 + 2 ^ (x + y - 1)) (2 ^ (2 * y)):= by exact Nat.Coprime.pow_right (2 * y) h2
            -- Show that 1 + 2^(x+y-1) divides 3^x * 2^(2*y)
            have h3 : 1 + 2 ^ (x + y - 1) ∣ 3 ^ x * 2 ^ (2 * y):= by rw [h] ; simp
            -- By coprimality, 1 + 2^(x+y-1) divides 3^x
            replace h3 : 1 + 2 ^ (x + y - 1) ∣ 3 ^ x:= by exact Nat.Coprime.dvd_of_dvd_mul_right h2 h3
            -- Prove that 3^x and 2^(x+y) are coprime
            replace h2 : Nat.Coprime (3 ^ x) (2 ^ (x + y)):= by exact Nat.Coprime.pow x (x + y) rfl
            -- Show that 3^x divides 2^(x+y) * (1 + 2^(x+y-1))
            have h4 : 3 ^ x ∣ 2 ^ (x + y) * (1 + 2 ^ (x + y - 1)):= by rw [←h] ; simp
            -- By coprimality, 3^x divides 1 + 2^(x+y-1)
            replace h4 : 3 ^ x ∣ 1 + 2 ^ (x + y - 1):= by exact Nat.Coprime.dvd_of_dvd_mul_left h2 h4
            -- By mutual divisibility, 1 + 2^(x+y-1) = 3^x
            replace h2 : 1 + 2 ^ (x + y - 1) = 3 ^ x:= by exact Nat.dvd_antisymm h3 h4
            clear h3 h4
            rw [h2] at h
            -- Deduce that 2^(2*y) = 2^(x+y)
            replace h : 2 ^ (2 * y) = 2 ^ (x + y):= by
                zify at h ⊢
                replace h : (3 : ℤ) ^ x * (2 ^ (2 * y) - 2 ^ (x + y)) = 0:= by linarith
                simp at h
                linarith
            -- Use logarithm properties to deduce that 2*y = x+y
            replace h : Nat.log 2 (2 ^ (2 * y)) = Nat.log 2 (2 ^ (x + y)):= by rw [h]
            rw [Nat.log_pow (by omega)] at h
            rw [Nat.log_pow (by omega)] at h
            -- This implies y = x
            replace h : y = x:= by omega
            subst y
            -- Substitute y = x and simplify
            rw [show x + x = 2 * x by ring] at h1 h2
            replace h2 : 2 + 2 * 2 ^ (2 * x - 1) = 2 * 3 ^ x:= by omega
            rw [show 2 * 2 ^ (2 * x - 1) = 2 ^ (1 + (2 * x - 1)) by ring] at h2
            rw [show 1 + (2 * x - 1) = 2 * x by omega] at h2
            rw [show 2 ^ (2 * x) = (2 ^ 2) ^ x by exact Nat.pow_mul 2 2 x] at h2
            ring_nf at h2
            -- Case analysis on x
            by_cases h3 : x = 1 ∨ x = 2
            .
                -- Handle the cases x = 1 and x = 2
                rcases h3 with h3 | h3
                all_goals
                    subst x
                    simp
            .
                -- Handle the case x ≥ 3
                replace h1 : x ≥ 3:= by omega
                clear h3
                set y:= x - 3 with hy
                clear_value y
                replace hy : x = y + 3:= by omega
                subst x
                ring_nf at h2
                -- Derive a contradiction for x ≥ 3
                have h3 : 3 ^ y > 0:= by positivity
                have h4 : 4 ≥ 3:= by omega
                replace h4 : 4 ^ y ≥ 3 ^ y:= by exact Nat.pow_le_pow_of_le_left h4 y
                linarith
    .
        -- Backward direction: if (x,y) is one of the three pairs, then it satisfies the equation
        intro h
        simp at h
        rcases h with h | h | h
        all_goals
            rcases h with ⟨hx, hy⟩
            subst x y
            simp
