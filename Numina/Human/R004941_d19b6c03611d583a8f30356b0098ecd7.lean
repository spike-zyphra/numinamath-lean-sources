import Mathlib
/- Positive real numbers $x, y, z$ satisfy $x y z+x y+y z+z x=x+y+z+1$. Prove that  $$ \frac{1}{3}\left(\sqrt{\frac{1+x^{2}}{1+x}}+\sqrt{\frac{1+y^{2}}{1+y}}+\sqrt{\frac{1+z^{2}}{1+z}}\right) \leq\left(\frac{x+y+z}{3}\right)^{5 / 8} . $$ -/
theorem inequalities_604729 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z + x * y + y * z + z * x = x + y + z + 1) : (1 / 3) * (√((1 + x ^ 2) / (1 + x)) + √((1 + y ^ 2) / (1 + y)) + √((1 + z ^ 2) / (1 + z))) ≤ ((x + y + z) / 3) ^ ((5 : ℝ) / 8):= by
        -- Key lemma: Simplifies the expression (1 + x^2)/(1 + x) into ((x + y)(x + z))/(1 + x + y + z)
        have h1 : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → x * y * z + x * y + y * z + z * x = x + y + z + 1 → (1 + x ^ 2) / (1 + x) = ((x + y) * (x + z)) / (1 + x + y + z):= by
            intro x y z hx hy hz h
            rw [show (1 + x ^ 2) / (1 + x) = (x * (x * y * z + x * y + x * z) + x ^ 2 + y * z + y + z + 1) / (2 * (1 + x + y + z)) by rw [show 2 * (1 + x + y + z) = (x + 1) * (y + 1) * (z + 1) by linarith] ; field_simp ; linarith]
            rw [show x * y * z + x * y + x * z = x + y + z + 1 - y * z by linarith]
            rw [show x * (x + y + z + 1 - y * z) + x ^ 2 + y * z + y + z + 1 = 2 * (x + y) * (x + z) by linarith]
            field_simp
            linarith
        rw [h1 x y z hx hy hz h]
        rw [h1 y z x hy hz hx (by linarith)]
        rw [h1 z x y hz hx hy (by linarith)]
        clear h1
        -- Key lemma: Cauchy-Schwarz inequality for 3D vectors
        -- For any positive real numbers x1,y1,z1,x2,y2,z2, we have:
        -- (x1^2 + y1^2 + z1^2)(x2^2 + y2^2 + z2^2) ≥ (x1x2 + y1y2 + z1z2)^2
        have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
                (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
                intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
                have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
                linarith
        -- Apply the inequality to specific vectors:
        -- (√(x+y), √(y+z), √(z+x)) and (√(x+z), √(y+x), √(z+y))
        specialize h1 √(x + y) √(y + z) √(z + x) √(x + z) √(y + x) √(z + y) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        -- refine the terms to match the inequality form
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [Real.sq_sqrt (by positivity)] at h1
        rw [show √(x + y) * √(x + z) = √((x + y) * (x + z)) by field_simp] at h1
        rw [show √(y + z) * √(y + x) = √((y + z) * (y + x)) by field_simp] at h1
        rw [show √(z + x) * √(z + y) = √((z + x) * (z + y)) by field_simp] at h1
        rw [show √((x + y) * (x + z) / (1 + x + y + z)) = √((x + y) * (x + z)) / √(1 + x + y + z) by field_simp]
        rw [show √((y + z) * (y + x) / (1 + y + z + x)) = √((y + z) * (y + x)) / √(1 + y + z + x) by field_simp]
        rw [show √((z + x) * (z + y) / (1 + z + x + y)) = √((z + x) * (z + y)) / √(1 + z + x + y) by field_simp]
        rw [show √((x + y) * (x + z)) / √(1 + x + y + z) = √((x + y) * (x + z)) * (1 / √(1 + x + y + z)) by field_simp]
        rw [show √((y + z) * (y + x)) / √(1 + y + z + x) = √((y + z) * (y + x)) * (1 / √(1 + y + z + x)) by field_simp]
        rw [show √((z + x) * (z + y)) / √(1 + z + x + y) = √((z + x) * (z + y)) * (1 / √(1 + z + x + y)) by field_simp]
        rw [show 1 + y + z + x = 1 + x + y + z by ring]
        rw [show 1 + z + x + y = 1 + x + y + z by ring]
        rw [show (√((x + y) * (x + z)) * (1 / √(1 + x + y + z)) + √((y + z) * (y + x)) * (1 / √(1 + x + y + z)) + √((z + x) * (z + y)) * (1 / √(1 + x + y + z))) = ((√((x + y) * (x + z)) + √((y + z) * (y + x)) + √((z + x) * (z + y))) * (1 / √(1 + x + y + z))) by ring]
        suffices ((√((x + y) * (x + z)) + √((y + z) * (y + x)) + √((z + x) * (z + y))) * (1 / √(1 + x + y + z))) ≤ 3 * ((x + y + z) / 3) ^ ((5 : ℝ) / 8) by linarith
        rw [show ((√((x + y) * (x + z)) + √((y + z) * (y + x)) + √((z + x) * (z + y))) * (1 / √(1 + x + y + z))) = ((√((x + y) * (x + z)) + √((y + z) * (y + x)) + √((z + x) * (z + y))) / √(1 + x + y + z)) by field_simp]
        suffices (√((x + y) * (x + z)) + √((y + z) * (y + x)) + √((z + x) * (z + y))) ≤ 3 * ((x + y + z) / 3) ^ ((5 : ℝ) / 8) * √(1 + x + y + z) by exact (div_le_iff₀ (by positivity)).mpr this
        rw [show (x + y + (y + z) + (z + x)) * (x + z + (y + x) + (z + y)) = (2 * (x + y + z)) ^ 2 by linarith] at h1
        replace h1 : |2 * (x + y + z)| ≥ |√((x + y) * (x + z)) + √((y + z) * (y + x)) + √((z + x) * (z + y))|:= by exact sq_le_sq.mp h1
        rw [abs_of_nonneg (by positivity)] at h1
        rw [abs_of_nonneg (by positivity)] at h1
        -- get the simplified inequality
        suffices 2 * (x + y + z) ≤ 3 * ((x + y + z) / 3) ^ ((5 : ℝ) / 8) * √(1 + x + y + z) by linarith
        clear h1
        set s:= x + y + z with hs
        rw [show 1 + x + y + z = 1 + s by linarith]
        replace hs : s > 0:= by linarith
        clear_value s
        clear hx hy hz h
        -- simplify the inequality by take the (4 : ℝ) power of both sides
        suffices 2 * s / √(1 + s) ≤ 3 * ((s / 3) ^ ((5 : ℝ) / 8)) by exact (mul_inv_le_iff₀ (by positivity)).mp this
        rw [show 2 * s / √(1 + s) = |2 * s / √(1 + s)| by exact Eq.symm (abs_of_nonneg (by positivity))]
        rw [show 3 * ((s / 3) ^ ((5 : ℝ) / 8)) = |3 * ((s / 3) ^ ((5 : ℝ) / 8))| by exact Eq.symm (abs_of_nonneg (by positivity))]
        suffices (2 * s / √(1 + s)) ^ 2 ≤ (3 * ((s / 3) ^ ((5 : ℝ) / 8))) ^ 2 by exact sq_le_sq.mp this
        rw [show (3 * (s / 3) ^ ((5 : ℝ) / 8)) ^ 2 = 9 * ((s / 3) ^ ((5 : ℝ) / 8)) ^ 2 by ring]
        rw [show ((s / 3) ^ ((5 : ℝ) / 8)) ^ 2 = ((s / 3) ^ ((5 : ℝ) / 8)) ^ (2 : ℝ) by norm_cast]
        rw [show ((s / 3) ^ ((5 : ℝ) / 8)) ^ (2 : ℝ) = (s / 3) ^ ((5 : ℝ) / 8 * 2) by refine Eq.symm (Real.rpow_mul (by positivity) (5 / 8) 2)]
        field_simp
        rw [show (5 : ℝ) * 2 / 8 = 5 * (1 / 4) by ring]
        rw [Real.rpow_mul (by positivity) 5 (1 / 4)]
        rw [show (2 * s) ^ 2 / (1 + s) = ((2 * s) ^ 2 / (1 + s)) ^ ((4 : ℝ) * (1 / 4)) by norm_num]
        rw [Real.rpow_mul (by positivity) 4 (1 / 4)]
        rw [show ((2 * s) ^ 2 / (1 + s)) ^ (4 : ℝ) = ((2 * s) ^ 2 / (1 + s)) ^ 4 by norm_cast]
        rw [show (9 : ℝ) = 9 ^ ((4 : ℝ) * (1 / 4)) by norm_num]
        rw [Real.rpow_mul (by positivity) 4 (1 / 4)]
        rw [show (9 : ℝ) ^ (4 : ℝ) = 9 ^ 4 by norm_cast]
        rw [show (s / 3) ^ (5 : ℝ) = (s / 3) ^ 5 by norm_cast]
        rw [Eq.symm (Real.mul_rpow (by positivity) (by positivity))]
        suffices ((2 * s) ^ 2 / (1 + s)) ^ 4 ≤ 9 ^ 4 * (s / 3) ^ 5 by refine
          (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by positivity)).mpr this
        field_simp
        have g1 : (1 + s) ^ 4 > 0:= by positivity
        -- prove the inequality by notice that s ^ 5 * (s - 3) ^ 2 * (27 * s ^ 2 + 14 * s + 3) ≥ 0
        suffices ((2 * s) ^ 2) ^ 4 ≤ 9 ^ 4 * s ^ 5 / 3 ^ 5 * (1 + s) ^ 4 by exact (div_le_iff₀ g1).mpr this
        ring_nf
        suffices s ^ 5 * (s - 3) ^ 2 * (27 * s ^ 2 + 14 * s + 3) ≥ 0 by linarith
        positivity
