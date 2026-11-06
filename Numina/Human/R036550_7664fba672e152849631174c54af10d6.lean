import Mathlib
/- Vind alle functies $f: \mathbb{Z}_ {>0} \rightarrow \mathbb{Z}_{>0}$ die voldoen aan

$$
f(f(f(n)))+f(f(n))+f(n)=3 n
$$

voor alle $n \in \mathbb{Z}_{>0}$. -/
theorem algebra_606186 (f : ℕ → ℕ) :
(∀ n, 0 < n → 0 < f n ∧ f (f (f n)) + f (f n) + f n = 3 * n) ↔
∀ n, 0 < n → f n = n:= by

-- Forward direction (⟹)
    constructor
    .
        intro h
        -- Proves that f is injective: if f(m) = f(n) then m = n
        have h1 : ∀ m n : ℕ, m > 0 → n > 0 → f m = f n → m = n:= by
            intro m n hm hn hmn
            have g1:= h n hn
            have g2:= h m hm
            replace g1:= g1.2
            replace g2:= g2.2
            rw [hmn] at g2
            linarith

        -- Inductive proof that f(n) = n for all positive n ≤ k + 1
        have h2 : ∀ k : ℕ, ∀ n : ℕ, 0 < n → n ≤ k + 1 → f n = n:= by
            intro k
            -- Base case: k = 0 (proves f(1) = 1)
            induction k with
            | zero =>
                intro n hn hn1
                simp at hn1
                replace hn1 : n = 1:= by omega
                subst n
                have g1:= (h 1 (by omega)).1
                have g2:= (h (f 1) g1).1
                have g3:= (h (f (f 1)) g2).1
                have g4:= (h 1 (by omega)).2
                linarith

            -- Inductive step: proves for k + 1 assuming it's true for k
            | succ k ih =>
                intro n hn hn1
                ring_nf at hn1
                rw [show 2 + k = k + 2 by ring] at hn1
                -- Proves f(k+2) ≥ k+2
                have g1 : f (k + 2) ≥ k + 2:= by
                    have g1:= (h (k + 2) (by omega)).1
                    by_contra H
                    simp at H
                    have g2:= ih (f (k + 2)) g1 (by omega)
                    specialize h1 (f (k + 2)) (k + 2) (by omega) (by omega) g2
                    linarith
                -- Proves f(f(k+2)) ≥ k+2
                have g2 : f (f (k + 2)) ≥ k + 2:= by
                    have g2:= (h (f (k + 2)) (by omega)).1
                    by_contra H
                    simp at H
                    have g3:= ih (f (f (k + 2))) g2 (by omega)
                    specialize h1 (f (f (k + 2))) (f (k + 2)) (by omega) (by omega) g3
                    linarith
                -- Proves f(f(f(k+2))) ≥ k+2
                have g3 : f (f (f (k + 2))) ≥ k + 2:= by
                    have g3:= (h (f (f (k + 2))) (by omega)).1
                    by_contra H
                    simp at H
                    have g4:= ih (f (f (f (k + 2)))) g3 (by omega)
                    specialize h1 (f (f (f (k + 2)))) (f (f (k + 2))) (by omega) (by omega) g4
                    linarith
                have g4:= (h (k + 2) (by omega)).2
                -- Case split on whether n ≤ k+1 or n = k+2
                by_cases hn : n ≤ k + 1
                .
                    specialize ih n (by omega) hn
                    exact ih
                .
                    replace hn : n = k + 2:= by omega
                    subst n
                    linarith

        -- Applies the inductive result to complete the forward direction
        intro n hn
        specialize h2 n n hn (by omega)
        exact h2

    -- Backward direction (⟸): trivial verification that f(n) = n satisfies the equation
    .
        intro h n hn
        specialize h n hn
        rw [h]
        rw [h]
        rw [h]
        constructor
        all_goals
            omega
