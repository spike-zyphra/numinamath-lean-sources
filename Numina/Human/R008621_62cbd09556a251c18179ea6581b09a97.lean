import Mathlib
/- Нека су $a, b$ и $c$ позитивни реални бројеви за које важи $a+b+c=1$. Доказати:

$$
\begin{array}{r}
a \sqrt{2 b+1}+b \sqrt{2 c+1}+c \sqrt{2 a+1} \leqslant \sqrt{2-\left(a^{2}+b^{2}+c^{2}\right)} \\
\text { (Никола Петровић) }
\end{array}
$$ -/
theorem algebra_608108 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
a * √(2 * b + 1) + b * √(2 * c + 1) + c * √(2 * a + 1) ≤ √(2 - (a ^ 2 + b ^ 2 + c ^ 2)) := by

    -- Helper lemma: Cauchy-Schwarz inequality for 3D vectors
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        -- Uses the fact that sum of squares is non-negative
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith

    -- Apply Cauchy-Schwarz to our specific vectors
    specialize h1 √(a * (2 * b + 1)) √(b * (2 * c + 1)) √(c * (2 * a + 1)) √a √b √c (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

    -- Series of simplifications using square root properties
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1

    -- Simplify expressions involving square roots
    rw [show √(a * (2 * b + 1)) = √a * √(2 * b + 1) by field_simp, show √a * √(2 * b + 1) * √a = √a ^ 2 * √(2 * b + 1) by ring_nf] at h1
    rw [show √(b * (2 * c + 1)) = √b * √(2 * c + 1) by field_simp, show √b * √(2 * c + 1) * √b = √b ^ 2 * √(2 * c + 1) by ring_nf] at h1
    rw [show √(c * (2 * a + 1)) = √c * √(2 * a + 1) by field_simp, show √c * √(2 * a + 1) * √c = √c ^ 2 * √(2 * a + 1) by ring_nf] at h1

    -- Simplify squared square roots
    rw [show √a ^ 2 = a by refine Real.sq_sqrt (by positivity)] at h1
    rw [show √b ^ 2 = b by refine Real.sq_sqrt (by positivity)] at h1
    rw [show √c ^ 2 = c by refine Real.sq_sqrt (by positivity)] at h1

    -- Use the condition a + b + c = 1
    rw [h] at h1
    simp at h1

    -- Algebraic manipulation
    rw [show a * (2 * b + 1) + b * (2 * c + 1) + c * (2 * a + 1) = 2 * (a * b + b * c + c * a) + (a + b + c) by ring_nf] at h1
    rw [h] at h1

    -- Key algebraic identity
    have h2 : 2 * (a * b + b * c + c * a) + 1 = 2 - (a ^ 2 + b ^ 2 + c ^ 2):= by
        have h2 : (a + b + c) ^ 2 = 1:= by
            rw [h]
            simp
        linarith
    rw [h2] at h1

    -- Final steps using square root properties
    replace h1 : √((a * √(2 * b + 1) + b * √(2 * c + 1) + c * √(2 * a + 1)) ^ 2) ≤ √(2 - (a ^ 2 + b ^ 2 + c ^ 2)):= by exact Real.sqrt_le_sqrt h1
    rw [show √((a * √(2 * b + 1) + b * √(2 * c + 1) + c * √(2 * a + 1)) ^ 2) = a * √(2 * b + 1) + b * √(2 * c + 1) + c * √(2 * a + 1) by field_simp] at h1
    exact h1
