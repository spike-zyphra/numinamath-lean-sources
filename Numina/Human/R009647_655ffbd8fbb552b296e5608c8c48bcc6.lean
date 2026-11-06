import Mathlib
/- On définit la suite $\left(a_{n}\right)$ par $a_{0}=a_{1}=a_{2}=1$ et si $n \geqslant 3$ :

$$
a_{n}=\left\lfloor\frac{n}{a_{n-1} a_{n-2} a_{n-3}}\right\rfloor
$$

Déterminer $\mathrm{a}_{2022}$. -/
theorem number_theory_607151 {a : ℕ → ℕ} (h0 : a 0 = 1) (h1 : a 1 = 1) (h2 : a 2 = 1) (han : ∀ n ≥ 3, a n = ⌊(n / (a (n - 1) * a (n - 2) * a (n - 3) : ℝ))⌋) :
a 2022 = 674:= by
    -- Rewrite the recurrence relation with index shift for easier use
    replace han : ∀ n : ℕ, a (n + 3) = ⌊((n + 3) / (a (n + 2) * a (n + 1) * a n : ℝ))⌋:= by
        intro n
        specialize han (n + 3) (by omega)
        rw [show n + 3 - 1 = n + 2 by omega] at han
        rw [show n + 3 - 2 = n + 1 by omega] at han
        rw [show n + 3 - 3 = n by omega] at han
        simp at han
        exact han

    -- Calculate a(3) = 3
    have h3 : a 3 = 3:= by
        zify
        specialize han 0
        norm_num at han
        rw [han, h0, h1, h2]
        simp

    -- Prove the pattern of the sequence using induction:
    -- For any k, we have:
    -- a(4k+4) = 1
    -- a(4k+5) = 1
    -- a(4k+6) = floor((4k+6)/3)
    -- a(4k+7) = 3
    have h4 : ∀ k : ℕ, (a (4 * k + 4) = 1 ∧ a (4 * k + 5) = 1 ∧ a (4 * k + 6) = ⌊(4 * k + 6) / (3 : ℝ)⌋ ∧ a (4 * k + 7) = 3):= by
        intro k
        induction k with
        | zero =>
            -- Base case: k = 0
            simp
            -- Calculate a(4) = 1
            have h4 : a 4 = 1:= by
                zify
                specialize han 1
                norm_num at han
                rw [han, h1, h2, h3]
                simp
                norm_num
            -- Calculate a(5) = 1
            have h5 : a 5 = 1:= by
                zify
                specialize han 2
                norm_num at han
                rw [han, h2, h3, h4]
                simp
                norm_num
            -- Calculate a(6) = 2
            have h6 : a 6 = 2:= by
                zify
                specialize han 3
                norm_num at han
                rw [han, h3, h4, h5]
                simp
                norm_num
            -- Calculate a(7) = 3
            have h7 : a 7 = 3:= by
                zify
                specialize han 4
                norm_num at han
                rw [han, h4, h5, h6]
                simp
                norm_num
            norm_num
            refine ⟨h4, h5, (by zify at h6 ; exact h6), h7⟩
        | succ k ih =>
            -- Inductive step: assuming the pattern holds for k, prove it for k+1
            rcases ih with ⟨_, ih1, ih2, ih3⟩
            -- Rewrite indices for clarity
            rw [show 4 * (k + 1) + 4 = 4 * k + 8 by omega]
            rw [show 4 * (k + 1) + 5 = 4 * k + 9 by omega]
            rw [show 4 * (k + 1) + 6 = 4 * k + 10 by omega]
            rw [show 4 * (k + 1) + 7 = 4 * k + 11 by omega]

            -- Establish lower bound for floor((4k+6)/3)
            have g2 : (4 * ↑k + 6) / (3 : ℝ) ≥ 2:= by
                suffices (↑k : ℝ) ≥ 0 by linarith
                simp
            replace g2 : ⌊(4 * ↑k + 6) / (3 : ℝ)⌋ ≥ 2:= by exact Int.le_floor.mpr g2
            rify at g2
            replace g2 : 3 * (↑⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ) > 0:= by linarith

            -- Prove a(4k+8) = 1
            have hk0 : a (4 * k + 8) = 1:= by
                zify
                specialize han (4 * k + 5)
                rw [show 4 * k + 5 + 3 = 4 * k + 8 by omega] at han
                rw [show 4 * k + 5 + 2 = 4 * k + 7 by omega] at han
                rw [show 4 * k + 5 + 1 = 4 * k + 6 by omega] at han
                rify at ih2
                rw [han, ih1, ih2, ih3]
                norm_num
                have g3 : (4 * ↑k + 5 + 3) / ((3 : ℝ) * ⌊(4 * ↑k + 6) / (3 : ℝ)⌋) < 2:= by
                    suffices (4 * ↑k + 5 + 3) < 2 * ((3 : ℝ) * ↑(⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ)) by exact (div_lt_iff₀ g2).mpr this
                    replace g4 : ⌊(4 * ↑k + 6) / (3 : ℝ)⌋ ≥ k + 2:= by exact Int.le_floor.mpr (by simp ; linarith)
                    rify at g4
                    linarith
                have g1 : (4 * ↑k + 5 + 3) / ((3 : ℝ) * ↑(⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ)) ≥ 1:= by
                    suffices (4 * ↑k + 5 + 3) ≥ 3 * (↑⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ) by exact (one_le_div₀ g2).mpr this
                    have g3:= Int.floor_le ((4 * ↑k + 6) / (3 : ℝ))
                    linarith
                set a:= (4 * ↑k + 5 + 3) / ((3 : ℝ) * ↑(⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ)) with ha
                clear_value a
                refine Int.floor_eq_iff.mpr (by simp ; refine ⟨(by linarith), (by linarith)⟩)

            -- Prove a(4k+9) = 1
            have hk1 : a (4 * k + 9) = 1:= by
                zify
                specialize han (4 * k + 6)
                rw [show 4 * k + 6 + 3 = 4 * k + 9 by omega] at han
                rw [show 4 * k + 6 + 2 = 4 * k + 8 by omega] at han
                rw [show 4 * k + 6 + 1 = 4 * k + 7 by omega] at han
                rify at ih2
                rw [han, ih2, ih3, hk0]
                norm_num
                have g3 : (4 * ↑k + 6 + 3) / ((3 : ℝ) * ⌊(4 * ↑k + 6) / (3 : ℝ)⌋) < 2:= by
                    suffices (4 * ↑k + 6 + 3) < 2 * ((3 : ℝ) * ↑(⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ)) by exact (div_lt_iff₀ g2).mpr this
                    replace g4 : ⌊(4 * ↑k + 6) / (3 : ℝ)⌋ ≥ k + 2:= by exact Int.le_floor.mpr (by simp ; linarith)
                    rify at g4
                    linarith
                have g1 : (4 * ↑k + 6 + 3) / ((3 : ℝ) * ↑(⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ)) ≥ 1:= by
                    suffices (4 * ↑k + 6 + 3) ≥ 3 * (↑⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ) by exact (one_le_div₀ g2).mpr this
                    have g3:= Int.floor_le ((4 * ↑k + 6) / (3 : ℝ))
                    linarith
                set a:= (4 * ↑k + 6 + 3) / ((3 : ℝ) * ↑(⌊(4 * ↑k + 6) / (3 : ℝ)⌋ : ℝ)) with ha
                clear_value a
                refine Int.floor_eq_iff.mpr (by simp ; refine ⟨(by linarith), (by linarith)⟩)

            -- Prove a(4k+10) = floor((4k+10)/3)
            have hk2 : a (4 * k + 10) = ⌊(4 * k + 10) / (3 : ℝ)⌋:= by
                specialize han (4 * k + 7)
                rw [show 4 * k + 7 + 3 = 4 * k + 10 by omega] at han
                rw [show 4 * k + 7 + 2 = 4 * k + 9 by omega] at han
                rw [show 4 * k + 7 + 1 = 4 * k + 8 by omega] at han
                rw [han, ih3, hk0, hk1]
                simp
                ring_nf

            -- Prove a(4k+11) = 3
            have hk3 : a (4 * k + 11) = 3:= by
                zify
                specialize han (4 * k + 8)
                rw [show 4 * k + 8 + 3 = 4 * k + 11 by omega] at han
                rw [show 4 * k + 8 + 2 = 4 * k + 10 by omega] at han
                rw [show 4 * k + 8 + 1 = 4 * k + 9 by omega] at han
                rify at hk2
                rw [han, hk2, hk0, hk1]
                simp
                rw [show 4 * (↑k : ℝ) + 8 + 3 = 4 * ↑k + 11 by linarith]
                set a:= (4 * (↑k : ℝ) + 11) / ↑⌊(4 * ↑k + 10) / (3 : ℝ)⌋ with ha
                clear_value a
                have g2 : (4 * ↑k + 10) / (3 : ℝ) ≥ 2:= by
                    suffices (↑k : ℝ) ≥ 0 by linarith
                    simp
                replace g2 : ⌊(4 * ↑k + 10) / (3 : ℝ)⌋ ≥ 2:= by exact Int.le_floor.mpr g2
                rify at g2
                replace g2 : (↑⌊(4 * ↑k + 10) / (3 : ℝ)⌋ : ℝ) > 0:= by linarith
                have ha1 : a ≥ 3:= by
                    rw [ha]
                    suffices (4 * (↑k : ℝ) + 11) ≥ 3 * ↑⌊(4 * ↑k + 10) / (3 : ℝ)⌋ by exact (le_div_iff₀ g2).mpr this
                    have g3:= Int.floor_le ((4 * ↑k + 10) / (3 : ℝ))
                    linarith
                have ha2 : a < 4:= by
                    rw [ha]
                    suffices (4 * (↑k : ℝ) + 11) < 4 * ↑⌊(4 * ↑k + 10) / (3 : ℝ)⌋ by exact (div_lt_iff₀ g2).mpr this
                    replace g4 : ⌊(4 * ↑k + 10) / (3 : ℝ)⌋ ≥ k + 3:= by exact Int.le_floor.mpr (by simp ; linarith)
                    rify at g4
                    linarith
                refine Int.floor_eq_iff.mpr (by simp ; refine ⟨(by linarith), (by linarith)⟩)
            simp
            rw [show 4 * ((↑k : ℝ) + 1) + 6 = 4 * ↑k + 10 by linarith]
            refine ⟨hk0, hk1, hk2, hk3⟩

    -- Apply the pattern to calculate a(2022)
    -- Since 2022 = 4* 505 + 2, and 4* 505 + 2 = 4* 504 + 6, we need a(4*504 + 6)
    specialize h4 504
    replace h4:= h4.2.2.1
    ring_nf at h4
    zify
    exact h4
