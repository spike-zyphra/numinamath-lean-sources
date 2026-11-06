import Mathlib
/- Trouver toutes les triplets d'entiers positifs $(x, y, z)$ satisfaisant l'équation

$$
x!+2^{y}=z!
$$ -/
theorem number_theory_607233 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ Nat.factorial x + 2 ^ y = Nat.factorial z} = {(2, 2, 3)}:= by
    -- We'll prove equality of sets by showing each element belongs to both sets
    ext ⟨x, y, z⟩
    constructor
    .
        -- First direction: if (x,y,z) satisfies the equation, then it must be (2,2,3)
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3, h4⟩
        -- Prove that factorial of numbers ≥ 2 is always even
        have h5 : ∀ x : ℕ, Even (Nat.factorial (x + 2)):= by
            intro x
            induction x with
            | zero =>
                simp
            | succ x ih =>
                rw [show x + 1 + 2 = x + 2 + 1 by ring]
                rw [Nat.factorial_succ]
                exact Even.mul_left ih (x + 2 + 1)
        -- Case analysis: either x = 1 or x ≥ 2
        by_cases hx : x = 1
        .
            -- Case x = 1
            subst x
            simp at h4
            -- 2^y is even
            have g1 : Even 2:= by decide
            replace g1 : Even (2 ^ y):= by exact (Nat.even_pow' (by omega)).mpr g1
            -- 1! + 2^y is odd
            replace g1 : Odd (1 + 2 ^ y):= by exact Even.one_add g1
            -- This means z must be at most 1
            have g2 : z ≤ 1:= by
                by_contra H
                simp at H
                specialize h5 (z - 2)
                rw [show z - 2 + 2 = z by omega] at h5
                rw [h4] at g1
                absurd g1
                simp
                exact h5
            -- So z is either 0 or 1
            replace g2 : z = 0 ∨ z = 1:= by omega
            rcases g2 with g2 | g2
            all_goals
                subst z
                simp at h4
        .
            -- Case x ≥ 2
            replace hx : x ≥ 2:= by omega
            -- Prove that x must be exactly 2
            replace hx : x = 2:= by
                by_contra H
                replace hx : x ≥ 3:= by omega
                clear H
                -- First, z must be greater than x
                have g1 : z > x:= by
                    by_contra H
                    simp at H
                    replace H : Nat.factorial z ≤ Nat.factorial x:= by exact Nat.factorial_le H
                    have g1 : 2 ^ y > 0:= by positivity
                    linarith
                -- Prove that 3 divides factorial of numbers ≥ 3
                have h6 : ∀ x : ℕ, 3 ∣ Nat.factorial (x + 3):= by
                    intro x
                    induction x with
                    | zero =>
                        simp [Nat.factorial_succ]
                        omega
                    | succ x ih =>
                        rw [show x + 1 + 3 = x + 3 + 1 by ring]
                        rw [Nat.factorial_succ]
                        exact Dvd.dvd.mul_left ih (x + 3 + 1)
                -- Apply the divisibility property
                have h7:= h6 (z - 3)
                specialize h6 (x - 3)
                rw [show z - 3 + 3 = z by omega] at h7
                rw [show x - 3 + 3 = x by omega] at h6
                rw [←h4] at h7
                -- This would mean 3 divides 2^y
                replace h7 : 3 ∣ 2 ^ y:= by exact (Nat.dvd_add_iff_right h6).mpr h7
                have g2 : Nat.Prime 3:= by norm_num
                -- Which means 3 divides 2, a contradiction
                replace h7 : 3 ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow g2 h7
                omega
            -- Now we know x = 2
            subst x
            simp at h4
            -- Case analysis: either y = 1 or y ≥ 2
            by_cases hy : y = 1
            .
                -- Case y = 1
                subst y
                simp at h4
                -- Show that z must be between 2 and 3
                have hz1 : z > 2:= by
                    by_contra H
                    simp at H
                    replace H : Nat.factorial z ≤ Nat.factorial 2:= by exact Nat.factorial_le H
                    simp at H
                    linarith
                have hz2 : z < 3:= by
                    by_contra H
                    simp at H
                    replace H : Nat.factorial 3 ≤ Nat.factorial z:= by exact Nat.factorial_le H
                    simp [Nat.factorial_succ] at H
                    linarith
                linarith
            .
                -- Case y ≥ 2
                replace hy : y ≥ 2:= by omega
                -- Rewrite 2^y as 4 * 2^(y-2)
                rw [show y = 2 + (y - 2) by omega] at h4
                rw [show 2 ^ (2 + (y - 2)) = 4 *  2 ^ (y - 2) by ring] at h4
                -- Show that z! ≡ 2 (mod 4)
                replace h5 : z.factorial ≡ 2 [MOD 4]:= by
                    rw [←h4]
                    have g1 : 4 ≡ 0 [MOD 4]:= by rfl
                    replace g1 : 4 * 2 ^ (y - 2) ≡ 0 * 2 ^ (y - 2) [MOD 4]:= by exact Nat.ModEq.mul g1 rfl
                    simp at g1
                    replace g1 : 2 + 4 * 2 ^ (y - 2) ≡ 2 + 0 [MOD 4]:= by exact Nat.ModEq.add_left 2 g1
                    simp at g1
                    exact g1
                -- Prove that 4 divides factorial of numbers ≥ 4
                have h6 : ∀ x : ℕ, 4 ∣ Nat.factorial (x + 4):= by
                    intro x
                    induction x with
                    | zero =>
                        simp [Nat.factorial_succ]
                        omega
                    | succ x ih =>
                        rw [show x + 1 + 4 = x + 4 + 1 by ring]
                        rw [Nat.factorial_succ]
                        exact Dvd.dvd.mul_left ih (x + 4 + 1)
                -- Show that z must be less than 4
                have h7 : z < 4:= by
                    by_contra H
                    simp at H
                    specialize h6 (z - 4)
                    rw [show z - 4 + 4 = z by omega] at h6
                    replace h6 : z.factorial ≡ 0 [MOD 4]:= by exact Nat.modEq_zero_iff_dvd.mpr h6
                    replace h5 : 2 ≡ 0 [MOD 4]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h6)) h5)
                    simp [Nat.ModEq] at h5
                -- Show that z must be greater than 1
                have h8 : z > 1:= by
                    by_contra H
                    simp at H
                    replace H : z = 0 ∨ z = 1:= by omega
                    rcases H with H | H
                    all_goals
                        subst z
                        simp [Nat.ModEq] at h5
                -- So z is either 2 or 3
                replace h7 : z = 2 ∨ z = 3:= by omega
                rcases h7 with h7 | h7
                .
                    -- Case z = 2
                    subst z
                    simp at h4
                .
                    -- Case z = 3
                    subst z
                    simp [Nat.factorial_succ] at h4
                    -- This means 2^(y-2) = 1
                    replace h4 : 2 ^ (y - 2) = 1:= by linarith
                    -- Which means y-2 = 0
                    replace h4 : y - 2 = 0:= by
                        by_contra H
                        replace H : y - 2 ≥ 1:= by omega
                        replace H : 2 ^ (y - 2) ≥ 2 ^ 1:= by exact Nat.pow_le_pow_of_le_right h1 H
                        linarith
                    -- So y = 2
                    replace h4 : y = 2:= by omega
                    subst y
                    simp
    .
        -- Second direction: prove that (2,2,3) satisfies the equation
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3⟩
        subst x y z
        simp [Nat.factorial_succ]
