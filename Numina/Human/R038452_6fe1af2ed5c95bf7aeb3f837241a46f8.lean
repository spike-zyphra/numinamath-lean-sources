import Mathlib
/- Laat $a, b$ en $c$ positieve reële getallen zijn met $a b c=1$. Bewijs dat

$$
a+b+c \geq \sqrt{\frac{(a+2)(b+2)(c+2)}{3}}
$$ -/
theorem algebra_605126 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a + b + c ≥ √((a + 2) * (b + 2) * (c + 2) / 3) := by
        -- Take cube roots of a, b, c to simplify the problem
        set x:= a ^ ((1 : ℝ) / 3) with hx
        set y:= b ^ ((1 : ℝ) / 3) with hy
        set z:= c ^ ((1 : ℝ) / 3) with hz
        -- Prove positivity of the cube roots
        have hxpos : x > 0:= by positivity
        have hypos : y > 0:= by positivity
        have hzpos : z > 0:= by positivity
        clear_value x y z
        -- Prove that cubing the cube root gives back the original number
        have h1 : ∀ a : ℝ, a > 0 → (a ^ ((1 : ℝ) / 3)) ^ 3 = a:= by
            intro a ha
            rw [show (a ^ ((1 : ℝ) / 3)) ^ 3 = (a ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast]
            rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3)]
            rw [show (1 : ℝ) / 3 * 3 = 1 by ring]
            simp
        -- Apply the cube root property to a, b, c
        have hxeq:= h1 a ha
        have hyeq:= h1 b hb
        have hzeq:= h1 c hc
        rw [←hx] at hxeq
        rw [←hy] at hyeq
        rw [←hz] at hzeq
        -- Show that the product of cube roots equals 1
        have hxyz : x * y * z = 1:= by
            rw [hx, hy, hz]
            rw [Eq.symm (Real.mul_rpow (by positivity) (by positivity))]
            rw [Eq.symm (Real.mul_rpow (by positivity) (by positivity))]
            rw [habc]
            simp
        rw [←hxeq, ←hyeq, ←hzeq]
        clear hx hy hz habc ha hb hc hxeq hyeq hzeq h1 a b c
        -- Main algebraic manipulation
        -- Transform the inequality into a form involving x, y, z
        replace hxyz : 2 * x * y * z = 2:= by linarith
        rw [←hxyz]
        rw [show (x ^ 3 + 2 * x * y * z) * (y ^ 3 + 2 * x * y * z) * (z ^ 3 + 2 * x * y * z) = (x * y * z) * (x ^ 2 + 2 * y * z) * (y ^ 2 + 2 * z * x) * (z ^ 2 + 2 * x * y) by ring]
        rw [show x * y * z = 1 by linarith]
        rw [show (1 * (x ^ 2 + 2 * y * z) * (y ^ 2 + 2 * z * x) * (z ^ 2 + 2 * x * y) / 3) = ((x ^ 2 + 2 * y * z) * (y ^ 2 + 2 * z * x) * (z ^ 2 + 2 * x * y) / 3) by simp]
        -- Apply AM-GM inequality to prove the key step
        have h1 : ((x ^ 2 + 2 * y * z) * (y ^ 2 + 2 * z * x) * (z ^ 2 + 2 * x * y) / 3) ≤ ((x + y + z) ^ 2) ^ 3 / 81:= by
            -- Use AM-GM inequality for three positive numbers
            have h1 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a * b * c ≤ ((a + b + c) / 3) ^ 3:= by
                intro a b c ha hb hc
                field_simp
                have h1 : (a - b) ^ 2 * (a + b) ≥ 0:= by positivity
                have h2 : (b - c) ^ 2 * (b + c) ≥ 0:= by positivity
                have h3 : (c - a) ^ 2 * (c + a) ≥ 0:= by positivity
                have h4 : c * (a - b) ^ 2 ≥ 0:= by positivity
                have h5 : b * (c - a) ^ 2 ≥ 0:= by positivity
                have h6 : a * (b - c) ^ 2 ≥ 0:= by positivity
                ring_nf
                linarith
            specialize h1 (x ^ 2 + 2 * y * z) (y ^ 2 + 2 * z * x) (z ^ 2 + 2 * x * y) (by positivity) (by positivity) (by positivity)
            rw [show (x ^ 2 + 2 * y * z + (y ^ 2 + 2 * z * x) + (z ^ 2 + 2 * x * y)) = (x + y + z) ^ 2 by ring] at h1
            rw [show ((x + y + z) ^ 2 / 3) ^ 3 = ((x + y + z) ^ 2) ^ 3 / 27 by ring] at h1
            linarith
        rw [show ((x + y + z) ^ 2) ^ 3 / 81 = ((x + y + z) ^ 3 / 9) ^ 2 by ring] at h1
        replace h1 : √((x ^ 2 + 2 * y * z) * (y ^ 2 + 2 * z * x) * (z ^ 2 + 2 * x * y) / 3) ≤ √(((x + y + z) ^ 3 / 9) ^ 2):= by exact Real.sqrt_le_sqrt h1
        rw [show √(((x + y + z) ^ 3 / 9) ^ 2) = (x + y + z) ^ 3 / 9 by exact Real.sqrt_sq (by positivity)] at h1
        suffices x ^ 3 + y ^ 3 + z ^ 3 ≥ (x + y + z) ^ 3 / 9 by linarith
        -- Final steps using algebraic inequalities
        -- Use the fact that squares of differences are non-negative
        have h2 : (x + y) * (x - y) ^ 2 + (y + z) * (y - z) ^ 2 + (z + x) * (z - x) ^ 2 ≥ 0:= by positivity
        have h3 : x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 ≥ 0:= by positivity
        linarith only [h2, h3]
