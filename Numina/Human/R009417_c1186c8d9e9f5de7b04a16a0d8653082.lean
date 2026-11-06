import Mathlib
/- Trouver tous les couples $(x, y)$ d'entiers strictement positifs tels que $x y \mid x^{2}+2 y-1$. -/
theorem number_theory_607411 : {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x * y ∣ x ^ 2 + 2 * y - 1} = {(1, y) | y > 0} ∪ {(3, 8), (5, 8)} ∪ {(2 * y - 1, y) | y > 0}:= by
    -- We'll prove equality of sets by showing each element belongs to one set if and only if it belongs to the other
    ext ⟨x, y⟩
    constructor
    -- Forward direction: if (x,y) satisfies the original condition, then it belongs to our claimed set
    .
        intro h
        simp at h
        rcases h with ⟨hx, hy, h⟩
        -- If x*y divides x^2 + 2*y - 1, then x divides x^2 + 2*y - 1
        have h1 : x ∣ x ^ 2 + 2 * y - 1:= by exact dvd_of_mul_right_dvd h
        -- x divides x^2 trivially
        have g1 : x ∣ x ^ 2:= by exact Dvd.intro_left (x.pow 1) rfl
        -- So x divides their difference: 2*y - 1
        replace h1 : x ∣ x ^ 2 + 2 * y - 1 - x ^ 2:= by exact Int.dvd_sub h1 g1
        ring_nf at h1
        rw [show -1 + y * 2 = 2 * y - 1 by linarith] at h1
        -- There exists an integer n such that 2*y - 1 = x*n
        replace h1 : ∃ n : ℤ, 2 * y - 1 = x * n:= by exact h1
        rcases h1 with ⟨n, hn⟩
        -- 2*y - 1 is odd
        replace g1 : Odd (2 * y - 1):= by simp [Odd] ; use (y - 1) ; linarith
        rw [hn] at g1
        -- Since 2*y - 1 = x*n is odd and their product is odd, both x and n must be odd
        have g2 : Odd n:= by exact Int.Odd.of_mul_right g1
        replace g1 : Odd x:= by exact Int.Odd.of_mul_left g1
        simp [Odd] at g2
        -- n = 2*k + 1 for some integer k
        rcases g2 with ⟨k, hk⟩
        subst n
        -- k must be non-negative
        have hk1 : k ≥ 0:= by
            by_contra H
            replace H : -(2 * k + 1) > 0:= by linarith
            replace H : x * (-(2 * k + 1)) > 0:= by positivity
            linarith
        -- The value x^2 + 2*y - 1 must be at least x*y
        have h1 : x ^ 2 + 2 * y - 1 ≥ x * y:= by
            replace h : ∃ m : ℤ, x ^ 2 + 2 * y - 1 = x * y * m:= by exact h
            rcases h with ⟨m, hm⟩
            have hmpos : m ≥ 1:= by
                by_contra H
                replace H : -m ≥ 0:= by linarith
                replace H : x * y * (-m) ≥ 0:= by positivity
                have g1 : x ^ 2 ≥ 0:= by positivity
                linarith
            rw [hm]
            replace hmpos : m - 1 ≥ 0:= by linarith
            replace hmpos : x * y * (m - 1) ≥ 0:= by positivity
            linarith
        -- Algebraic manipulation to derive constraints on x and k
        replace h1 : x * (2 * x + 4 * k + 1 - x * (2 * k + 1)) ≥ 0:= by rw [←hn] ; linarith
        replace h1 : 2 * x + 4 * k + 1 - x * (2 * k + 1) ≥ 0:= by exact nonneg_of_mul_nonneg_right h1 hx
        replace h1 : x * (2 * k - 1) ≤ 4 * k + 1:= by linarith
        -- Case analysis on k
        by_cases hk2 : k ≥ 3
        -- Case 1: k ≥ 3
        .
            -- In this case, x must be 1
            have h2 : x < 2:= by
                by_contra H
                simp at H
                have H1 : x ≠ 2:= by
                    by_contra H1
                    rw [H1] at g1
                    absurd g1
                    simp
                replace H : x ≥ 3:= by omega
                replace hk1 : 2 * k - 1 ≥ 0:= by linarith
                replace H : 3 * (2 * k - 1) ≤ x * (2 * k - 1):= by exact Int.mul_le_mul_of_nonneg_right H hk1
                linarith
            replace h2 : x = 1:= by omega
            subst x
            simp
            left
            exact hy
        -- Case 2: k < 3
        .
            -- k must be 0, 1, or 2
            replace hk2 : k = 0 ∨ k = 1 ∨ k = 2:= by omega
            rcases hk2 with hk2 | hk2 | hk2
            -- Subcase: k = 0
            .
                subst k
                simp at hn
                rw [←hn]
                simp
                right
                exact hy
            -- Subcase: k = 1
            .
                subst k
                simp at h1 hn
                simp [Odd] at g1
                rcases g1 with ⟨x1, hx1⟩
                replace h1 : x1 = 0 ∨ x1 = 1 ∨ x1 = 2:= by omega
                rcases h1 with h1 | h1 | h1
                -- x = 1
                .
                    subst x1
                    simp at hx1
                    subst x
                    simp
                    left
                    exact hy
                -- x = 3
                .
                    subst x1
                    simp at hx1
                    subst x
                    replace hn : y = 5:= by omega
                    subst y
                    simp at h
                    omega
                -- x = 5
                .
                    subst x1
                    simp at hx1
                    subst x
                    replace hn : y = 8:= by omega
                    subst y
                    simp
            -- Subcase: k = 2
            .
                subst k
                simp at h1
                replace h1 : x ≤ 3:= by omega
                have h2 : x ≠ 2:= by
                    by_contra H
                    rw [H] at g1
                    absurd g1
                    simp
                replace h1 : x = 1 ∨ x = 3:= by omega
                clear h2
                rcases h1 with h1 | h1
                -- x = 1
                .
                    subst x
                    simp
                    left
                    exact hy
                -- x = 3
                .
                    subst x
                    replace hn : y = 8:= by omega
                    subst y
                    simp
    -- Reverse direction: if (x,y) belongs to our claimed set, then it satisfies the original condition
    .
        intro h
        simp at h
        rcases h with h | h
        -- Case: (x,y) is in {(1,y) | y > 0} or {(3,8), (5,8)}
        .
            rcases h with h | h | h
            -- Subcase: (x,y) = (3,8)
            .
                rcases h with ⟨hx, hy⟩
                subst x y
                simp
            -- Subcase: (x,y) = (5,8)
            .
                rcases h with ⟨hx, hy⟩
                subst x y
                simp
            -- Subcase: (x,y) = (1,y) for y > 0
            .
                rcases h with ⟨hx, hy⟩
                rw [←hy]
                simp
                exact hx
        -- Case: (x,y) is in {(2*y - 1, y) | y > 0}
        .
            rcases h with ⟨hx, hy⟩
            rw [←hy]
            simp
            refine ⟨(by omega), hx, ?_⟩
            rw [show (2 * y - 1) ^ 2 + 2 * y - 1 = (2 * y - 1) * y * 2 by ring]
            simp
