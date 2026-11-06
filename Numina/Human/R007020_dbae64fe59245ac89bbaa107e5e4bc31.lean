import Mathlib
/- Let $a, b$ and $c$ be positive real numbers such that $a b c=8$. Prove that

$$
\frac{a^{2}}{\sqrt{\left(1+a^{3}\right)\left(1+b^{3}\right)}}+\frac{b^{2}}{\sqrt{\left(1+b^{3}\right)\left(1+c^{3}\right)}}+\frac{c^{2}}{\sqrt{\left(1+c^{3}\right)\left(1+a^{3}\right)}} \geq \frac{4}{3} .
$$ -/
theorem algebra_604948 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 8) :
4 / 3 ≤ a ^ 2 / √((1 + a ^ 3) * (1 + b ^ 3)) + b ^ 2 / √((1 + b ^ 3) * (1 + c ^ 3)) +
c ^ 2 / √((1 + c ^ 3) * (1 + a ^ 3)):= by
    -- Key lemma: For any positive real x, 1/√(1+x³) ≥ 2/(2+x²)
    have h1 : ∀ x : ℝ, x > 0 → 1 / √(1 + x ^ 3) ≥ 2 / (2 + x ^ 2):= by
        intro x hx
        rw [show 1 / √(1 + x ^ 3) = |1 / √(1 + x ^ 3)| by exact Eq.symm (abs_of_nonneg (by positivity))]
        rw [show 2 / (2 + x ^ 2) = |2 / (2 + x ^ 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]
        suffices (1 / √(1 + x ^ 3)) ^ 2 ≥ (2 / (2 + x ^ 2)) ^ 2 by exact sq_le_sq.mp this
        field_simp
        have g1 : (2 + x ^ 2) ^ 2 > 0:= by positivity
        norm_num
        field_simp
        suffices 4 ≤ (1 / (1 + x ^ 3)) * (2 + x ^ 2) ^ 2 by exact (div_le_iff₀ g1).mpr this
        have g2 : 1 + x ^ 3 > 0:= by positivity
        field_simp
        suffices 4 * (1 + x ^ 3) ≤ (2 + x ^ 2) ^ 2 by exact (le_div_iff₀ g2).mpr this
        suffices x ^ 2 * (x - 2) ^ 2 ≥ 0 by linarith
        positivity
    -- Apply the lemma to a, b, and c
    have h2:= h1 a ha
    have h3:= h1 b hb
    have h4:= h1 c hc
    clear h1
    -- Multiply inequalities pairwise
    have h5 : 1 / √(1 + a ^ 3) * (1 / √(1 + b ^ 3)) ≥ 2 / (2 + a ^ 2) * (2 / (2 + b ^ 2)):= by refine mul_le_mul h2 h3 (by positivity) (by positivity)
    have h6 : 1 / √(1 + b ^ 3) * (1 / √(1 + c ^ 3)) ≥ 2 / (2 + b ^ 2) * (2 / (2 + c ^ 2)):= by refine mul_le_mul h3 h4 (by positivity) (by positivity)
    have h7 : 1 / √(1 + c ^ 3) * (1 / √(1 + a ^ 3)) ≥ 2 / (2 + c ^ 2) * (2 / (2 + a ^ 2)):= by refine mul_le_mul h4 h2 (by positivity) (by positivity)
    clear h2 h3 h4
    -- Rewrite expressions to use the product form
    rw [show a ^ 2 / √((1 + a ^ 3) * (1 + b ^ 3)) = a ^ 2 * (1 / √(1 + a ^ 3) * (1 / √(1 + b ^ 3))) by field_simp]
    rw [show b ^ 2 / √((1 + b ^ 3) * (1 + c ^ 3)) = b ^ 2 * (1 / √(1 + b ^ 3) * (1 / √(1 + c ^ 3))) by field_simp]
    rw [show c ^ 2 / √((1 + c ^ 3) * (1 + a ^ 3)) = c ^ 2 * (1 / √(1 + c ^ 3) * (1 / √(1 + a ^ 3))) by field_simp]
    -- Prove positivity of squares
    have h2 : a ^ 2 > 0:= by positivity
    have h3 : b ^ 2 > 0:= by positivity
    have h4 : c ^ 2 > 0:= by positivity
    -- Apply multiplication to inequalities
    replace h5 : a ^ 2 * (1 / √(1 + a ^ 3) * (1 / √(1 + b ^ 3))) ≥ a ^ 2 * (2 / (2 + a ^ 2) * (2 / (2 + b ^ 2))):= by exact (mul_le_mul_iff_of_pos_left h2).mpr h5
    replace h6 : b ^ 2 * (1 / √(1 + b ^ 3) * (1 / √(1 + c ^ 3))) ≥ b ^ 2 * (2 / (2 + b ^ 2) * (2 / (2 + c ^ 2))):= by exact (mul_le_mul_iff_of_pos_left h3).mpr h6
    replace h7 : c ^ 2 * (1 / √(1 + c ^ 3) * (1 / √(1 + a ^ 3))) ≥ c ^ 2 * (2 / (2 + c ^ 2) * (2 / (2 + a ^ 2))):= by exact (mul_le_mul_iff_of_pos_left h4).mpr h7
    clear h2 h3 h4

    -- By transitivity, if we prove the lower bound for the right-hand side, we're done
    suffices a ^ 2 * (2 / (2 + a ^ 2) * (2 / (2 + b ^ 2))) + b ^ 2 * (2 / (2 + b ^ 2) * (2 / (2 + c ^ 2))) + c ^ 2 * (2 / (2 + c ^ 2) * (2 / (2 + a ^ 2))) ≥ 4 / 3 by linarith
    clear h5 h6 h7

    -- Simplify the expressions using field operations
    rw [show a ^ 2 * (2 / (2 + a ^ 2) * (2 / (2 + b ^ 2))) = 4 * a ^ 2 / ((2 + a ^ 2) * (2 + b ^ 2)) by field_simp ; linarith]
    rw [show b ^ 2 * (2 / (2 + b ^ 2) * (2 / (2 + c ^ 2))) = 4 * b ^ 2 / ((2 + b ^ 2) * (2 + c ^ 2)) by field_simp ; linarith]
    rw [show c ^ 2 * (2 / (2 + c ^ 2) * (2 / (2 + a ^ 2))) = 4 * c ^ 2 / ((2 + c ^ 2) * (2 + a ^ 2)) by field_simp ; linarith]

    -- Key transformation: Use c = 8/(ab) to rewrite the sum in a more manageable form
    rw [show 4 * a ^ 2 / ((2 + a ^ 2) * (2 + b ^ 2)) + 4 * b ^ 2 / ((2 + b ^ 2) * (2 + c ^ 2)) +
    4 * c ^ 2 / ((2 + c ^ 2) * (2 + a ^ 2)) = 2 / (1 + 36 / (2 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) by rw [show c = 8 / (a * b) by field_simp ; linarith] ; field_simp ; linarith]

    -- Prove that the denominator term is at least 72
    have h1 : 2 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ 72:= by
        -- First lemma: For positive reals, x³ + y³ + z³ ≥ 3xyz
        have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
            intro x y z hx hy hz
            -- Express in terms of squares of differences
            have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
            rw [h1]
            positivity

        -- Apply the lemma to cube roots to get a more general inequality
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

        -- Apply the inequality to squares and products of squares
        have g1:= h1 (a ^ 2) (b ^ 2) (c ^ 2) (by positivity) (by positivity) (by positivity)
        have g2:= h1 (a ^ 2 * b ^ 2) (b ^ 2 * c ^ 2) (c ^ 2 * a ^ 2) (by positivity) (by positivity) (by positivity)

        -- Use the fact that abc = 8 to simplify
        rw [show a ^ 2 * b ^ 2 * c ^ 2 = (a * b * c) ^ 2 by ring_nf] at g1
        rw [show a ^ 2 * b ^ 2 * (b ^ 2 * c ^ 2) * (c ^ 2 * a ^ 2) = (a * b * c) ^ 4 by ring_nf] at g2
        rw [habc] at g1 g2
        rw [show (8 : ℝ) ^ 2 = 4 ^ 3 by norm_num, show (4 : ℝ) ^ 3 = 4 ^ (3 : ℝ) by norm_cast] at g1
        rw [show (8 : ℝ) ^ 4 = 16 ^ 3 by norm_num, show (16 : ℝ) ^ 3 = 16 ^ (3 : ℝ) by norm_cast] at g2
        rw [Eq.symm (Real.rpow_mul (by linarith) 3 (1 / 3))] at g1 g2
        rw [show (3 : ℝ) * (1 / 3) = 1 by ring_nf] at g1 g2
        simp at g1 g2
        linarith

    -- Define t as the denominator term for cleaner notation
    set t:= 2 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 with ht
    clear_value t
    field_simp

    -- Final inequality to prove: 4/3 * (t + 36) ≤ 2t
    suffices 4 / 3 * (t + 36) ≤ 2 * t by exact (le_div_iff₀ (by linarith)).mpr this
    linarith
