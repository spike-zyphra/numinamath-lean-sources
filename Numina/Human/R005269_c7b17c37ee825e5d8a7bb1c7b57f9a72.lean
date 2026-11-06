import Mathlib
/- Trouver tous les entiers $p$ tels que $p, p+2$ et $p+4$ soient tous les 3 premiers?
Un nombre premier est un entier $\geqslant 2$ qui n'est divisible que par 1 et lui-même. -/
theorem number_theory_607284 (p : ℕ) : p.Prime ∧ (p + 2).Prime ∧ (p + 4).Prime ↔ p = 3 := by
    -- Split the proof into two directions: forward (⟹) and backward (⟸)
    constructor
    -- Forward direction: if p, p+2, and p+4 are all prime, then p = 3
    .
        -- Assume p, p+2, and p+4 are all prime
        intro h
        -- Destructure the hypothesis into three separate prime conditions
        rcases h with ⟨h1, h2, h3⟩
        -- Consider all possible cases for p modulo 3
        mod_cases hp : p % 3
        -- Case 1: p ≡ 0 (mod 3)
        .
            -- If p ≡ 0 (mod 3), then 3 divides p
            replace h4 : 3 ∣ p:= by exact Nat.dvd_of_mod_eq_zero hp
            -- Since p is prime, if 3 divides p, then either 3 = 1 or 3 = p
            replace h4 : 3 = 1 ∨ 3 = p:= by exact (Nat.dvd_prime h1).mp h4
            -- Simplify the disjunction
            simp at h4
            -- Derive a contradiction using linear arithmetic
            linarith
        -- Case 2: p ≡ 1 (mod 3)
        .
            -- If p ≡ 1 (mod 3), then p+2 ≡ 1+2 ≡ 3 ≡ 0 (mod 3)
            replace hp : p + 2 ≡ 1 + 2 [MOD 3]:= by exact Nat.ModEq.add_right 2 hp
            -- Verify that 1+2 ≡ 0 (mod 3)
            have g1 : 1 + 2 ≡ 0 [MOD 3]:= by rfl
            -- Therefore p+2 ≡ 0 (mod 3)
            replace hp : p + 2 ≡ 0 [MOD 3]:= by exact Nat.ModEq.trans hp g1
            -- This means 3 divides p+2
            replace h4 : 3 ∣ p + 2:= by exact Nat.dvd_of_mod_eq_zero hp
            -- Since p+2 is prime, if 3 divides p+2, then either 3 = 1 or 3 = p+2
            replace h4 : 3 = 1 ∨ 3 = p + 2:= by exact (Nat.dvd_prime h2).mp h4
            -- Simplify the disjunction
            simp at h4
            -- Since p is prime, p > 1
            have hp1 : p > 1:= by exact Nat.Prime.one_lt h1
            -- Derive a contradiction using linear arithmetic
            linarith
        -- Case 3: p ≡ 2 (mod 3)
        .
            -- If p ≡ 2 (mod 3), then p+4 ≡ 2+4 ≡ 6 ≡ 0 (mod 3)
            replace hp : p + 4 ≡ 2 + 4 [MOD 3]:= by exact Nat.ModEq.add_right 4 hp
            -- Verify that 2+4 ≡ 0 (mod 3)
            have g1 : 2 + 4 ≡ 0 [MOD 3]:= by rfl
            -- Therefore p+4 ≡ 0 (mod 3)
            replace hp : p + 4 ≡ 0 [MOD 3]:= by exact Nat.ModEq.trans hp g1
            -- This means 3 divides p+4
            replace h4 : 3 ∣ p + 4:= by exact Nat.dvd_of_mod_eq_zero hp
            -- Since p+4 is prime, if 3 divides p+4, then either 3 = 1 or 3 = p+4
            replace h4 : 3 = 1 ∨ 3 = p + 4:= by exact (Nat.dvd_prime h3).mp h4
            -- Simplify the disjunction
            simp at h4
    -- Backward direction: if p = 3, then p, p+2, and p+4 are all prime
    .
        -- Assume p = 3
        intro h
        -- Substitute p with 3
        subst p
        -- Simplify the goal
        simp
        -- Verify that 3, 5, and 7 are all prime using norm_num
        norm_num
