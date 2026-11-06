import Mathlib

/- Let $F$ be an increasing real function defined for all $x, 0 \leq x \leq 1$, satisfying the conditions

$$
\begin{aligned}
& F\left(\frac{x}{3}\right)=\frac{F(x)}{2} \\
& F(1-x)=1-F(x)
\end{aligned}
$$

Determine $F\left(\frac{173}{1993}\right)$ and $F\left(\frac{1}{13}\right)$. -/
theorem algebra_607940 (F : ℝ → ℝ) (hF : Monotone F) (h1 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → F (x / 3) = F x / 2) (h2 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → F (1 - x) = 1 - F x) : F (173 / 1993) = 3 / 16 ∧ F (1 / 13) = 1 / 7 := by
    -- Unfold the definition of Monotone
    simp [Monotone] at hF
    -- Prove F(0) = 0 using the first condition with x = 0
    have h3 : F 0 = 0:= by
        specialize h1 0 ⟨(by linarith), (by linarith)⟩
        simp at h1
        linarith
    -- Prove F(1) = 1 using the second condition with x = 1
    have h4 : F 1 = 1:= by
        specialize h2 1 ⟨(by linarith), (by linarith)⟩
        simp at h2
        linarith
    -- Prove F(1/3) = 1/2 using the first condition with x = 1
    have h5 : F (1 / 3) = 1 / 2:= by
        specialize h1 1 ⟨(by linarith), (by linarith)⟩
        simp at h1
        simp
        rw [h1, h4]
        simp
    -- Prove F(2/3) = 1/2 using the second condition with x = 1/3
    have h6 : F (2 / 3) = 1 / 2:= by
        specialize h2 (1 / 3) ⟨(by linarith), (by linarith)⟩
        ring_nf at h2
        linarith
    -- Key lemma: F(x) = 1/2 for all x in [1/3, 2/3] due to monotonicity
    have h7 : ∀ x : ℝ, 1 / 3 ≤ x ∧ x ≤ 2 / 3 → F x = 1 / 2:= by
        intro x ⟨hx1, hx2⟩
        have g1:= hF hx1
        have g2:= hF hx2
        rw [h5] at g1
        rw [h6] at g2
        linarith
    constructor
    -- First part: Prove F(173/1993) = 3/16
    .
        clear h3 h4 h5 h6
        -- Apply various conditions and use the fact that certain values fall in [1/3, 2/3]
        have g1:= h1 (1557 / 1993) ⟨(by linarith), (by linarith)⟩
        have g2:= h1 (519 / 1993) ⟨(by linarith), (by linarith)⟩
        have g3:= h2 (436 / 1993) ⟨(by linarith), (by linarith)⟩
        have g4:= h1 (1308 / 1993) ⟨(by linarith), (by linarith)⟩
        ring_nf at g1 g2 g3 g4
        specialize h7 (1308 / 1993) ⟨(by linarith), (by linarith)⟩
        linarith
    -- Second part: Prove F(1/13) = 1/7
    .
        -- Apply various conditions to derive the value
        have g1:= h2 (12 / 13) ⟨(by linarith), (by linarith)⟩
        have g2:= h1 (12 / 13) ⟨(by linarith), (by linarith)⟩
        have g3:= h2 (9 / 13) ⟨(by linarith), (by linarith)⟩
        have g4:= h1 (9 / 13) ⟨(by linarith), (by linarith)⟩
        have g5:= h1 (3 / 13) ⟨(by linarith), (by linarith)⟩
        ring_nf at g1 g2 g3 g4 g5
        linarith
