import Mathlib
/- Given $a, b, c>0$ such that $a^{2}<16 b c$, $b^{2}<16 a c$ and $c^{2}<16 a b$. Prove that

$$
a^{2}+b^{2}+c^{2}<2(a b+b c+a c)
$$ -/
theorem algebra_607154 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ^ 2 < 16 * b * c) (h2 : b ^ 2 < 16 * a * c) (h3 : c ^ 2 < 16 * a * b) :
    a ^ 2 + b ^ 2 + c ^ 2 < 2 * (a * b + b * c + a * c) := by
        -- First, prove a key lemma: if x²<16yz then √x < √y + √z
        have h4 : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a ^ 2 < 16 * b * c → b ^ 2 < 16 * a * c → c ^ 2 < 16 * a * b → √a < √b + √c:= by
            intro a b c ha hb hc h1 _ _
            rw [show √b = b ^ ((1 : ℝ) / 2) by exact Real.sqrt_eq_rpow b]
            rw [show √c = c ^ ((1 : ℝ) / 2) by exact Real.sqrt_eq_rpow c]
            have g1 : (b ^ ((1 : ℝ) / 4) - c ^ ((1 : ℝ) / 4)) ^ 2 ≥ 0:= by positivity
            ring_nf at g1
            rw [show (b ^ ((1 : ℝ) / 4)) ^ 2 = (b ^ ((1 : ℝ) / 4)) ^ (2 : ℝ) by norm_cast] at g1
            rw [show (c ^ ((1 : ℝ) / 4)) ^ 2 = (c ^ ((1 : ℝ) / 4)) ^ (2 : ℝ) by norm_cast] at g1
            rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 4) 2)] at g1
            rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 4) 2)] at g1
            rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at g1
            rw [show (1 : ℝ) / 4 * 2 = 1 / 2 by ring_nf] at g1
            replace h1 : b * c > a ^ 2 / 16:= by linarith
            rw [show a ^ 2 / 16 = (a / 4) ^ 2 by ring_nf] at h1
            replace h1 : (b * c) ^ ((1 : ℝ) / 4) > ((a / 4) ^ 2) ^ ((1 : ℝ) / 4):= by refine (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by positivity)).mpr h1
            rw [show (a / 4) ^ 2 = (a / 4) ^ (2 : ℝ) by norm_cast] at h1
            rw [Eq.symm (Real.rpow_mul (show a / 4 ≥ 0 by positivity) 2 (1 / 4))] at h1
            rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by ring_nf] at h1
            rw [show (a / 4) ^ ((1 : ℝ) / 2) = √(a / 4) by exact Eq.symm (Real.sqrt_eq_rpow (a / 4))] at h1
            rw [show a = √a ^ 2 by refine Eq.symm (Real.sq_sqrt (by linarith))] at h1
            rw [show √a ^ 2 / 4 = (√a / 2) ^ 2 by ring_nf] at h1
            rw [show √((√a / 2) ^ 2) = √a / 2 by refine Real.sqrt_sq (by positivity)] at h1
            linarith
        -- Apply the lemma to different permutations of a, b, c
        have g1:= h4 b c a hb hc ha (by linarith) (by linarith) (by linarith)
        have g2:= h4 a c b ha hc hb (by linarith) (by linarith) (by linarith)
        have g3:= h4 c a b hc ha hb (by linarith) (by linarith) (by linarith)
        -- Rearrange inequalities to get |√a - √b| < √c
        replace g1 : √b - √a < √c:= by linarith
        replace g2 : √a - √b < √c:= by linarith
        have g4 : |√a - √b| < √c:= by refine abs_sub_lt_iff.mpr ⟨g2, g1⟩
        -- Handle absolute values and squares
        rw [show √c = |√c| by exact Eq.symm (abs_of_pos (by positivity))] at g3 g4
        rw [show √a + √b = |√a + √b| by exact Eq.symm (abs_of_pos (by positivity))] at g3
        replace g4 : (√a - √b) ^ 2 < √c ^ 2:= by exact sq_lt_sq.mpr g4
        replace g3 : √c ^ 2 < (√a + √b) ^ 2:= by exact sq_lt_sq.mpr g3
        -- Simplify expressions involving squares and square roots
        rw [show √c ^ 2 = c by refine Real.sq_sqrt (by linarith)] at g3 g4
        ring_nf at g3 g4
        rw [Real.sq_sqrt (by linarith)] at g3 g4
        rw [Real.sq_sqrt (by linarith)] at g3 g4
        rw [show √a * √b = √(a * b) by refine Eq.symm (Real.sqrt_mul' a (by linarith))] at g3 g4
        -- Final algebraic manipulations to reach the conclusion
        replace g3 : a + b - c + √(a * b) * 2 > 0:= by linarith
        replace g4 : √(a * b) * 2 - (a + b - c) > 0:= by linarith
        have g5 : (a + b - c + √(a * b) * 2) * (√(a * b) * 2 - (a + b - c)) > 0:= by positivity
        replace g5 : (a + b - c) ^ 2 < 4 * √(a * b) ^ 2:= by linarith
        rw [show √(a * b) ^ 2 = a * b by refine Real.sq_sqrt (by positivity)] at g5
        linarith
