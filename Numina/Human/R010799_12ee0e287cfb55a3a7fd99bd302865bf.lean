import Mathlib
/- Soient $\mathrm{a}, \mathrm{b}$ et c trois nombres strictement positifs tels que $\mathrm{a}+\mathrm{b}+\mathrm{c}+\mathrm{abc}=4$. Montrer que

$$
\left(1+\frac{\mathrm{a}}{\mathrm{~b}}+\mathrm{ca}\right)\left(1+\frac{\mathrm{b}}{\mathrm{c}}+\mathrm{ab}\right)\left(1+\frac{\mathrm{c}}{\mathrm{a}}+\mathrm{bc}\right) \geqslant 27
$$ -/

theorem algebra_607686 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c + a * b * c = 4) : (1 + a / b + c * a) * (1 + b / c + a * b) * (1 + c / a + b * c) ≥ 27:= by

    -- Lemma 1: For positive real numbers x, y, z,
    -- prove that x³ + y³ + z³ - 3xyz ≥ 0 (Schur's inequality)
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- Express in terms of squares of differences
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity

    -- Lemma 2: Transform Schur's inequality using cube roots
    -- For positive real numbers x, y, z,
    -- prove that x + y + z - 3(xyz)^(1/3) ≥ 0
    replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
        intro x y z hx hy hz
        specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
        rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h1
        rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h1
        rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h1
        simp at h1
        simp
        linarith

    -- Prove that abc ≤ 1 using the previous lemma
    have h2 : a * b * c ≤ 1:= by
        by_contra H
        simp at H
        specialize h1 a b c ha hb hc
        have h2 : (a * b * c) ^ ((1 : ℝ) / 3) > 1:= by refine Real.one_lt_rpow H (by linarith)
        linarith

    -- Express the product in terms of reciprocals
    have h3 : (1 + a / b + c * a) * (1 + b / c + a * b) * (1 + c / a + b * c) = 15 + 4 * (1 / a + 1 / b + 1 / c):= by
        field_simp
        replace h : c = (4 - a - b) / (a * b + 1):= by field_simp ; linarith
        subst c
        field_simp
        ring_nf

    -- Prove that 1/a + 1/b + 1/c ≥ 3 using the transformed Schur's inequality
    have h4 : 1 / a + 1 / b + 1 / c ≥ 3:= by
        specialize h1 (1 / a) (1 / b) (1 / c) (by positivity) (by positivity) (by positivity)
        rw [show (1 / a) * (1 / b) * (1 / c) = 1 / (a * b * c) by field_simp] at h1
        have g1 : a * b * c > 0:= by positivity
        replace h2 : 1 / (a * b * c) ≥ 1:= by exact one_le_one_div g1 h2
        replace h2 : (1 / (a * b * c)) ^ ((1 : ℝ) / 3) ≥ 1:= by refine Real.one_le_rpow h2 (by linarith)
        linarith

    -- Complete the proof using the previous results
    linarith
