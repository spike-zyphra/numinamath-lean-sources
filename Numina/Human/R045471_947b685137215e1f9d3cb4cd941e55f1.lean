import Mathlib
/- For any real number a, let $\lfloor a\rfloor$ denote the greatest integer not exceeding a. In positive real numbers solve the following equation

$$
n+\lfloor\sqrt{n}\rfloor+\lfloor\sqrt[3]{n}\rfloor=2014
$$ -/
theorem number_theory_605585 (n : ℕ) (hn : n > 0) : n + ⌊√n⌋ + ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ = 2014 ↔ n = 1958:= by
    -- This lemma proves that for any natural number n between 1950 and 2000, the floor of its square root equals 44
    have h3 : ∀ n : ℕ, n ≥ 1950 → n ≤ 2000 → ⌊√n⌋ = 44:= by
        intro n h1 h2
        refine Int.floor_eq_iff.mpr ?_
        constructor
        .
            rify at h1 h2
            replace h1 : (↑n : ℝ) ≥ 44 ^ 2:= by linarith
            replace h1 : √n ≥ √(44 ^ 2):= by exact Real.sqrt_le_sqrt h1
            field_simp at h1
            simp
            exact h1
        .
            rify at h1 h2
            simp
            ring_nf
            replace h2 : (n : ℝ) ≤ (449 / 10) ^ 2:= by linarith
            replace h2 : √n ≤ √((449 / 10) ^ 2):= by exact Real.sqrt_le_sqrt h2
            field_simp at h2
            simp
            linarith
    -- This lemma proves that for any natural number n between 1950 and 2000, the floor of its cube root equals 12
    have h4 : ∀ n : ℕ, n ≥ 1950 → n ≤ 2000 → ⌊(↑n : ℝ) ^ ((1 : ℝ) / 3)⌋ = 12:= by
        intro n h1 h2
        refine Int.floor_eq_iff.mpr ?_
        constructor
        .
            rify at h1 h2
            replace h1 : (↑n : ℝ) ≥ 12 ^ 3:= by linarith
            replace h1 : (↑n : ℝ) ^ ((1 : ℝ) / 3) ≥ (12 ^ 3) ^ ((1 : ℝ) / 3):= by exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
            rw [show (12 : ℝ) ^ 3 = 12 ^ (3 : ℝ) by norm_cast] at h1
            rw [Eq.symm (Real.rpow_mul (by positivity) 3 (1 / 3))] at h1
            ring_nf at h1
            simp
            field_simp
            linarith
        .
            norm_num
            rify at h1 h2
            replace h2 : (n : ℝ) ≤ (129 / 10) ^ 3:= by linarith
            replace h2 : (↑n : ℝ) ^ ((1 : ℝ) / 3) ≤ ((129 / 10) ^ 3) ^ ((1 : ℝ) / 3):= by exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
            rw [show ((129 : ℝ) / 10) ^ 3 = (129 / 10) ^ (3 : ℝ) by norm_cast] at h2
            rw [Eq.symm (Real.rpow_mul (by positivity) 3 (1 / 3))] at h2
            ring_nf at h2
            linarith
    -- Begin the main proof with a bidirectional implication
    constructor
    -- Forward direction: if n + ⌊√n⌋ + ⌊n^(1/3)⌋ = 2014, then n = 1958
    .
        intro h
        -- Prove that n ≥ 1950 by contradiction
        have h1 : n ≥ 1950:= by
            by_contra H
            simp at H
            -- If n < 1950, then √n < 45
            have g1 : √n < 45:= by
                by_contra H1
                simp at H1
                replace H1 : √n ^ 2 ≥ 45 ^ 2:= by nlinarith only [H1]
                field_simp at H1
                rify at H
                linarith
            -- If n < 1950, then n^(1/3) < 20
            have g2 : (↑n : ℝ) ^ ((1 : ℝ) / 3) < 20:= by
                by_contra H1
                simp at H1
                field_simp at H1
                have g2 : (20 : ℝ) ≥ 0:= by linarith
                replace H1 : ((↑n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) ≥ 20 ^ (3 : ℝ):= by refine Real.rpow_le_rpow g2 H1 (by linarith)
                rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 3) 3)] at H1
                simp at H1
                rify at H
                linarith
            -- Therefore ⌊√n⌋ < 45 and ⌊n^(1/3)⌋ < 20
            replace g1 : ⌊√n⌋ < 45:= by exact Int.floor_lt.mpr g1
            replace g2 : ⌊(↑n : ℝ) ^ ((1 : ℝ) / 3)⌋ < 20:= by exact Int.floor_lt.mpr g2
            linarith
        -- Prove that n ≤ 2000 by contradiction
        have h2 : n ≤ 2000:= by
            by_contra H
            simp at H
            -- If n > 2000, then √n ≥ 44
            have g1 : √n ≥ 44:= by
                by_contra H1
                simp at H1
                rify at H
                replace H : (n : ℝ) ≥ (441 / 10) ^ 2:= by linarith
                replace H : √n ≥ √((441 / 10) ^ 2):= by exact Real.sqrt_le_sqrt H
                field_simp at H
                linarith
            -- n^(1/3) is always non-negative
            have g2 : (↑n : ℝ) ^ ((1 : ℝ) / 3) ≥ 0:= by positivity
            -- Therefore ⌊√n⌋ ≥ 44 and ⌊n^(1/3)⌋ ≥ 0
            replace g1 : ⌊√n⌋ ≥ 44:= by exact Int.le_floor.mpr g1
            replace g2 : ⌊(↑n : ℝ) ^ ((1 : ℝ) / 3)⌋ ≥ 0:= by exact Int.floor_nonneg.mpr g2
            linarith
        -- Apply the lemmas to determine that n = 1958
        specialize h3 n h1 h2
        specialize h4 n h1 h2
        zify
        linarith
    -- Reverse direction: if n = 1958, then n + ⌊√n⌋ + ⌊n^(1/3)⌋ = 2014
    .
        intro h1
        specialize h3 n (by linarith) (by linarith)
        specialize h4 n (by linarith) (by linarith)
        rw [h3, h4, h1]
        simp
