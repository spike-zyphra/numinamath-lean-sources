import Mathlib
/- Soit $\left(x_{n}\right)_ {n \in \mathbb{N}}$ une suite réelle telle que $x_{0}=0$ et $x_{1}=1$ et pour tout $n \geqslant 0, x_{n+2}=$ $3 x_{n+1}-2 x_{n}$. On pose également $y_{n}=x_{n}^{2}+2^{n+2}$ pour tout entier naturel $n$. Montrer que pour tout entier $n>0, y_{n}$ est le carré d'un entier impair. -/
theorem algebra_607329 (x : ℕ → ℝ) (y : ℕ → ℝ)
(h0 : x 0 = 0) (h1 : x 1 = 1) (h2 : ∀ n, x (n + 2) = 3 * x (n + 1) - 2 * x n) (h3 : ∀ n, y n = x n ^ 2 + 2 ^ (n + 2)) :
∀ n > 0, ∃ m : ℕ, m ^ 2 = y n ∧ Odd m:= by
    -- First, we prove by induction that x_n = 2^n - 1 for all n
    have g1 : ∀ n : ℕ, x n = 2 ^ n - 1 ∧ x (n + 1) = 2 ^ (n + 1) - 1:= by
        intro n
        induction n with
        | zero =>
            -- Base case: n = 0
            simp [h0, h1]
            linarith
        | succ n ih =>
            -- Inductive step
            constructor
            .
                exact ih.2
            .
                rw [show n + 1 + 1 = n + 2 by omega]
                rcases ih with ⟨ih1, ih2⟩
                rw [h2 n, ih1, ih2]
                ring_nf
    -- Simplify the previous result to get just x_n = 2^n - 1
    replace g1 : ∀ n : ℕ, x n = 2 ^ n - 1:= by
        intro n
        rcases g1 n with ⟨h1, _⟩
        exact h1
    -- Now we prove the main theorem
    intro n hn
    -- We claim that m = 2^n + 1 is the odd integer we're looking for
    use (2 ^ n + 1)
    simp
    constructor
    .
        -- First, we show that (2^n + 1)^2 = y_n
        specialize h3 n
        rw [h3, g1 n]
        ring_nf
    .
        -- Then, we prove that 2^n + 1 is odd
        suffices ∃ k : ℕ, 2 ^ n + 1 = 2 * k + 1 by exact this
        use (2 ^ (n - 1))
        rw [show 2 * 2 ^ (n - 1) = 2 ^ (1 + (n - 1)) by ring_nf]
        rw [show 1 + (n - 1) = n by omega]
