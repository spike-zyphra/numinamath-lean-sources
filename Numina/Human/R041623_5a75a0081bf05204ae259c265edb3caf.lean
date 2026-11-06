import Mathlib
/- Gegeven zijn reële getallen $a, b$ en $c$ waarvoor geldt dat $0 \leq a \leq b \leq c$ en $a+b+c=1$. Bewijs dat

$$
a b \sqrt{b-a}+b c \sqrt{c-b}+a c \sqrt{c-a}<\frac{1}{4}
$$ -/
theorem algebra_605937 (a b c : ℝ) (h1 : 0 ≤ a) (h2 : a ≤ b) (h3 : b ≤ c) (h4 : a + b + c = 1) :
a * b * √(b - a) + b * c * √(c - b) + a * c * √(c - a) < 1 / 4 := by
    -- Lemma: For any x ≤ y, √(y-x) ≤ (1 + y - x)/2
    have h5 : ∀ x y : ℝ, x ≤ y → √(y - x) ≤ (1 + y - x) / 2:= by
        intro x y hxy
        have h5 : (√(y - x) - 1) ^ 2 ≥ 0:= by positivity
        ring_nf at h5
        rw [show √(y - x) ^ 2 = y - x by refine Real.sq_sqrt (by linarith)] at h5
        linarith
    -- Prove a*b ≥ 0 using transitivity of inequalities
    have g1 : a * b ≥ 0:= by
        replace h2 : b ≥ 0:= by linarith
        positivity
    -- Prove b*c ≥ 0 using transitivity of inequalities
    have g2 : b * c ≥ 0:= by
        replace h2 : b ≥ 0:= by linarith
        replace h3 : c ≥ 0:= by linarith
        positivity
    -- Prove a*c ≥ 0 using transitivity of inequalities
    have g3 : a * c ≥ 0:= by
        replace h3 : c ≥ 0:= by linarith
        positivity
    -- Apply the lemma to each term
    replace g1 : a * b * √(b - a) ≤ a * b * ((1 + b - a) / 2):= by exact mul_le_mul_of_nonneg_left (h5 a b h2) g1
    replace g2 : b * c * √(c - b) ≤ b * c * ((1 + c - b) / 2):= by exact mul_le_mul_of_nonneg_left (h5 b c h3) g2
    replace g3 : a * c * √(c - a) ≤ a * c * ((1 + c - a) / 2):= by exact mul_le_mul_of_nonneg_left (h5 a c (by linarith)) g3
    -- Prove various inequalities involving powers
    have g4 : a * b ^ 2 ≤ b ^ 3:= by
        replace h2 : b - a ≥ 0:= by linarith
        replace h2 : b ^ 2 * (b - a) ≥ 0:= by positivity
        linarith
    have g5 : a * c ^ 2 ≤ b * c ^ 2:= by
        replace h2 : b - a ≥ 0:= by linarith
        replace h2 : c ^ 2 * (b - a) ≥ 0:= by positivity
        linarith
    -- Prove non-negativity of expressions
    have g6 : (b - c) ^ 2 * c ≥ 0:= by
        replace h3 : c ≥ 0:= by linarith
        positivity
    -- Use the fact that (a + b + c)³ = 1
    have g7 : (a + b + c) ^ 3 = 1:= by
        rw [h4]
        ring_nf
    -- Proof by contradiction
    by_contra H
    simp at H
    rw [show (4 : ℝ)⁻¹= 1 / 4 by ring_nf] at H
    -- Simplify expressions using the sum condition
    rw [show 1 + b - a = 2 * b + c by linarith] at g1
    rw [show 1 + c - b = 2 * c + a by linarith] at g2
    rw [show 1 + c - a = 2 * c + b by linarith] at g3
    -- Prove more non-negativity conditions
    have g8 : a ^ 2 * b ≥ 0:= by
        replace h2 : b ≥ 0:= by linarith
        positivity
    have g9 : a ^ 3 ≥ 0:= by positivity
    have g10 : a ^ 2 * c ≥ 0:= by
        replace h3 : c ≥ 0:= by linarith
        positivity
    have g11 : b ^ 2 * c ≥ 0:= by
        replace h3 : c ≥ 0:= by linarith
        replace _ : b ≥ 0:= by linarith
        positivity
    -- Deduce that a³ = 0 and b²c = 0
    replace g9 : a ^ 3 = 0:= by linarith
    replace g11 : b ^ 2 * c = 0:= by linarith
    -- Therefore a = 0 and either b² = 0 or c = 0
    replace g9 : a = 0:= by exact pow_eq_zero g9
    replace g11 : b ^ 2 = 0 ∨ c = 0:= by exact mul_eq_zero.mp g11
    rcases g11 with g11 | g11
    -- Case 1: If b² = 0, then b = 0
    .
        replace g11 : b = 0:= by exact pow_eq_zero g11
        subst a b
        simp at h4
        subst c
        ring_nf at H
        linarith
    -- Case 2: If c = 0, then b = 0 by previous inequalities
    .
        replace h2 : b = 0:= by linarith
        subst a b c
        simp at h4
