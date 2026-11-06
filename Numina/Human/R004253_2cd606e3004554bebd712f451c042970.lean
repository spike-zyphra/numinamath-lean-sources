import Mathlib

/- A triangle is called a parabolic triangle if its vertices lie on a parabola $y=x^{2}$.
Prove that for every nonnegative integer $n$, there is an odd number $m$ and
a parabolic triangle with vertices at three distinct points with integer coordinates with area $\left(2^{n} m\right)^{2}$ 。-/

theorem geometry_245576 (n : ℕ):
  ∃ m : ℤ, Odd m ∧
  ∃ x1 y1 x2 y2 x3 y3: ℤ,
    y1 = x1 ^ 2 ∧ y2 = x2 ^ 2 ∧ y3 = x3 ^ 2 ∧
    ((1: ℝ) / 2) * |x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2)| =
    (2^n * m) ^ 2 := by

    by_cases r: n = 0

    -- case n = 0
    .
        use 1
        refine ⟨(by norm_num),?_⟩
        use 1, 1, -1, 1, 0, 0
        norm_num
        simp [r]

    -- case 0 < n
    .
        replace r: 1 ≤ n := by omega
        use 2 ^ (4 * n - 2) - 1
        constructor
        .
            rw [odd_iff_exists_bit1]
            use (2 ^ (4 * n - 3) - 1)
            rw [show 4 * n - 2 = 4 * n - 3 + 1 by omega]
            set q:= 4 * n - 3
            clear_value q
            ring
        .
            set a:= (2: ℤ) ^ (2 * n)
            set b:= (2: ℤ) ^ (4 * n - 2) + 1
            use a, a ^ 2, -a, a ^ 2, b, b ^ 2
            refine ⟨(by ring), (by ring), (by ring), ?_⟩
            have s: a * (a ^ 2 - b ^ 2) + -a * (b ^ 2 - a ^ 2) + b * (a ^ 2 - a ^ 2) = 2 * a * (a ^ 2 - b ^ 2) := by
                clear_value a b
                ring
            rw [s]
            clear s
            have i: |2 * a * (a ^ 2 - b ^ 2)| = -(2 * a * (a ^ 2 - b ^ 2)) := by
                apply abs_of_nonpos
                suffices a ^ 2 - b ^ 2 ≤ 0 by
                    have u: 0 ≤ a := by
                        simp [a]
                    clear_value a b
                    nlinarith
                rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring]
                suffices a ≤ b by
                    have oa: 0 ≤ a := by simp [a]
                    have ob: 0 ≤ b := by
                        linarith
                    clear_value a b
                    nlinarith
                simp [a, b]
                suffices 2 ^ (2 * n) ≤ 2 ^ (4 * n - 2) by linarith
                apply Nat.pow_le_pow_of_le_right
                norm_num
                omega
            rw [i]
            clear i
            set q:= (2: ℤ) ^ n
            rify
            have f1: a = q ^ 2 := by
                simp [a, q]
                ring
            rify at f1
            have f2: b = q ^ 4 / (4: ℝ) + 1 := by
                simp [b, q]
                suffices (4: ℝ) * 2 ^ (4 * n - 2) = (2 ^ n) ^ 4 by
                    rw [← this]
                    ring
                norm_cast
                nth_rewrite 1 [show 4 = 2 ^ 2 by norm_num]
                rw [← pow_add]
                rw [show 2 + (4 * n - 2) = n * 4 by omega]
                rw [pow_mul]
            rw [show (2: ℝ) ^ n = q by simp [q]]
            have f3: 2 ^ (4 * n - 2) = b - 1 := by
                simp [b]
            rify at f3
            simp [f1, f2, f3]
            ring