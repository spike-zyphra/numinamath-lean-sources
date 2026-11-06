import Mathlib

/-
All ordered pairs of real numbers \((x, y)\) are to be determined for which the system of equations

\[
\begin{aligned}
x \cdot\left(a x^{2}+b y^{2}-a\right) & =0 \\
y \cdot\left(a x^{2}+b y^{2}-b\right) & =0
\end{aligned}
\]

is satisfied. Here, \(a\) and \(b\) are real numbers with \(a \neq 0, b \neq 0\) and \(a \neq b\). -/

theorem algebra_196400: {(x, y): ℝ × ℝ | ∃ a b: ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ x * (a * x ^ 2 + b * y ^ 2 - a) = 0 ∧
    y * (a * x ^ 2 + b * y ^ 2 - b) = 0} = {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)} := by

    ext ⟨x, y⟩
    constructor
    
    -- the forward direction
    .
        intro h
        simp only [Set.mem_setOf] at h
        obtain ⟨a, b, nea, neb, ne, ha, hb⟩ := h
        simp
        by_cases lx: x = 0

        -- case x = 0
        .
            clear ha
            simp [lx] at hb
            rcases hb with h | h
            .
                simp [lx, h]
            .
                replace h: b * (y ^ 2 - 1) = 0 := by linarith
                simp [neb] at h
                rw [show y ^ 2 - 1 = (y + 1) * (y - 1) by ring] at h
                simp at h
                rcases h with h | h
                .
                    simp [lx]
                    right
                    right
                    linarith

                .
                    simp [h, lx]
                    right
                    left
                    linarith

        -- case x ≠ 0
        .
            simp [lx] at ha
            have o: y = 0 := by -- then we must have y = 0
                by_contra! o
                simp [o] at hb
                have s: b = a := by nlinarith
                simp [s] at ne
            clear hb
            simp [o] at ha
            replace h: a * (x ^ 2 - 1) = 0 := by linarith
            simp [nea] at h
            rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring] at h
            simp at h
            rcases h with h | h
            .
                simp [o]
                right
                right
                linarith

            .
                simp [o]
                right
                left
                linarith

    -- backward direction
    .
        intro h
        simp at h
        simp only [Set.mem_setOf]
        rcases h with h | h | h | h | h
        all_goals simp only [h]
        .
            use 1
            use 2
            norm_num
        .
            use 1
            use 2
            norm_num
        .
            use 1
            use 2
            norm_num
        .
            use 1
            use 2
            norm_num
        .
            use 1
            use 2
            norm_num