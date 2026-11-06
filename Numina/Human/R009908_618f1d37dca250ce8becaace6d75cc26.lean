import Mathlib

/- Нека је $n \geqslant 2$ природан број и нека позитивни реални бројеви $a_{0}, a_{1}, \ldots, a_{n}$ задовољавају једнакост

$$
\left(a_{k-1}+a_{k}\right)\left(a_{k}+a_{k+1}\right)=a_{k-1}-a_{k+1} \quad \text { за свако } k=1,2, \ldots, n-1 \text {. }
$$

Доказати да је $a_{n}<\frac{1}{n-1}$.

(Душан Ђукић) -/
theorem algebra_608072 (n : ℕ) (a : ℕ → ℝ) (hn : 2 ≤ n) (hpos : ∀ k : ℕ, k ≥ 0 ∧ k ≤ n → 0 < a k)
    (h : ∀ k : ℕ, k ≥ 1 ∧ k ≤ n - 1 → (a (k - 1) + a k) * (a k + a (k + 1)) = a (k - 1) - a (k + 1)) :
    a n < 1 / (n - 1) := by
    -- Transform the main equation into a recursive form:
    -- 1/(aₖ + aₖ₊₁) = 1/(aₖ₋₁ + aₖ) + 1
    replace h : ∀ k : ℕ, k ≥ 1 ∧ k ≤ n - 1 → 1 / (a k + a (k + 1)) = 1 / (a (k - 1) + a k) + 1:= by
        intro k hk
        specialize h k hk
        have g1:= hpos (k - 1) ⟨(by omega), (by omega)⟩
        have g2:= hpos k ⟨(by omega), (by omega)⟩
        have g3:= hpos (k + 1) ⟨(by omega), (by omega)⟩
        field_simp
        linarith
    -- Prove by induction that:
    -- 1/(aₖ + aₖ₊₁) = 1/(a₀ + a₁) + k
    have h1 : ∀ k : ℕ, k ≥ 1 → k ≤ n - 1 → 1 / (a k + a (k + 1)) = 1 / (a 0 + a 1) + k:= by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base =>
            intro h1
            specialize h 1 ⟨(by omega), (by omega)⟩
            rw [show 1 - 1 = 0 by omega] at h
            simp at h
            simp
            exact h
        | succ m hm ih =>
            intro h1
            replace ih:= ih (by omega)
            specialize h (m + 1) ⟨(by omega), (by omega)⟩
            rw [h]
            rw [show m + 1 - 1 = m by omega]
            rw [ih]
            simp
            linarith
    -- Apply the formula to k = n-1
    specialize h1 (n - 1) (by omega) (by omega)
    -- Collect positivity facts for various terms
    have g1:= hpos 0 ⟨(by omega), (by omega)⟩
    have g2:= hpos 1 ⟨(by omega), (by omega)⟩
    have g3:= hpos (n - 1) ⟨(by omega), (by omega)⟩
    have g4:= hpos n ⟨(by omega), (by omega)⟩
    -- Show 1/(a₀ + a₁) is positive
    have g5 : 1 / (a 0 + a 1) > 0:= by positivity
    rw [show n - 1 + 1 = n by omega] at h1
    -- Derive that 1/(aₙ₋₁ + aₙ) > n-1
    replace h1: 1 / (a (n - 1) + a n) > ↑(n - 1):= by linarith

    -- Use that aₙ₋₁ + aₙ > aₙ to get 1/(aₙ₋₁ + aₙ) < 1/aₙ
    have g6 : a (n - 1) + a n > a n:= by linarith
    replace g6 : 1 / (a (n - 1) + a n) < 1 / a n:= by exact one_div_lt_one_div_of_lt g4 g6

    -- Combine inequalities to show 1/aₙ > n-1
    replace h1 : 1 / a n > ↑(n - 1):= by linarith

    -- Final algebraic manipulations to conclude aₙ < 1/(n-1)
    have g7 : (n - 1) + 1 = n:= by omega
    rify at g7
    replace g7 : (↑(n - 1) : ℝ) = (↑n : ℝ)  - 1:= by linarith
    rw [g7] at h1
    rify at hn
    replace hn : (↑n : ℝ) - 1 > 0:= by linarith
    exact (lt_one_div hn g4).mp h1
