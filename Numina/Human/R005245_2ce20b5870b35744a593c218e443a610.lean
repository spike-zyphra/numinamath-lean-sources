import Mathlib
/- Let $x, y, z$ be positive numbers such that

$$
\frac{1}{x}+\frac{1}{y}+\frac{1}{z}=1
$$

Show that

$$
\sqrt{x+y z}+\sqrt{y+z x}+\sqrt{z+x y} \geq \sqrt{x y z}+\sqrt{x}+\sqrt{y}+\sqrt{z}
$$ -/

theorem algebra_607117 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 1 / x + 1 / y + 1 / z = 1) :
√(x + y * z) + √(y + z * x) + √(z + x * y) ≥ √(x * y * z) + √x + √y + √z := by

    -- Helper lemma 1: Cauchy-Schwarz inequality for 2D vectors
    have h1 : ∀ a b c d : ℝ, (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ≥ (a * c + b * d) ^ 2:= by
        intro a b c d
        have h1 : (a * d - b * c) ^ 2 ≥ 0:= by positivity
        linarith

    -- Helper lemma 2: Key inequality for one term of the sum
    -- Proves that √(a + b* c) ≥ √(a*b *c)/a + √a when 1/a + 1/b + 1/c = 1
    have h2 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → 1 / a + 1 / b + 1 / c = 1 → √(a + b * c) ≥ √(a * b * c) * (1 / a) + √a:= by
        intro a b c ha hb hc h
        -- Rewrite the left side using the condition 1/a + 1/b + 1/c = 1
        rw [show a + b * c = (a * b * c) * (1 / a * (1 / a + 1 / b + 1 / c) + 1 / b * (1 / c)) by rw [h] ; field_simp ; ring_nf]
        rw [show 1 / a * (1 / a + 1 / b + 1 / c) + 1 / b * (1 / c) = (1 / a + 1 / b) * (1 / a + 1 / c) by ring]
        rw [show √(a * b * c * ((1 / a + 1 / b) * (1 / a + 1 / c))) = √(a * b * c) * √((1 / a + 1 / b) * (1 / a + 1 / c)) by field_simp]
        specialize h1 √(1 / a) √(1 / b) √(1 / a) √(1 / c)
        -- Simplify square roots
        rw [show √(1 / a) * √(1 / a) = √(1 / a) ^ 2 by ring] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [show √(1 / b) * √(1 / c) = √(1 / b * (1 / c)) by field_simp] at h1
        rw [show 1 / b * (1 / c) = 1 / (b * c) by field_simp] at h1
        replace h1 : √((1 / a + 1 / b) * (1 / a + 1 / c)) ≥ √((1 / a + √(1 / (b * c))) ^ 2):= by exact Real.sqrt_le_sqrt h1
        rw [show √((1 / a + √(1 / (b * c))) ^ 2) = 1 / a + √(1 / (b * c)) by field_simp] at h1
        have g1 : √(a * b * c) ≥ 0:= by positivity
        replace h1 : √(a * b * c) * √((1 / a + 1 / b) * (1 / a + 1 / c)) ≥ √(a * b * c) * (1 / a + √(1 / (b * c))):= by exact mul_le_mul_of_nonneg_left h1 g1
        have g2 : √(a * b * c) * √(1 / (b * c)) = √(a * b * c * (1 / (b * c))):= by field_simp
        rw [show a * b * c * (1 / (b * c)) = a by field_simp ; linarith] at g2
        linarith

    -- Apply helper lemma 2 to each cyclic permutation of (x,y,z)
    have h3:= h2 x y z hx hy hz h
    have h4:= h2 y z x hy hz hx (by linarith)
    have h5:= h2 z x y hz hx hy (by linarith)

    -- Simplify expressions involving cyclic permutations
    rw [show y * z * x = x * y * z by ring] at h4
    rw [show z * x * y = x * y * z by ring] at h5

    -- Final step: Combine the inequalities using the original condition
    have h6 : √(x * y * z) * (1 / x) + √(x * y * z) * (1 / y) + √(x * y * z) * (1 / z) = √(x * y * z) * (1 / x + 1 / y + 1 / z):= by ring
    rw [h] at h6
    linarith
