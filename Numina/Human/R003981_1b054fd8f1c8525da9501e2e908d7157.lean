import Mathlib
set_option maxHeartbeats 5000000

open Real



/- 2. Given positive numbers $a, b, c, d$. Find the minimum value of the expression


$$

A=\left(\frac{a+b}{c}\right)^{4}+\left(\frac{b+c}{d}\right)^{4}+\left(\frac{c+d}{a}\right)^{4}+\left(\frac{d+a}{b}\right)^{4}

$$
 -/
theorem inequalities_226874 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : ℝ) (hA : A = ((a + b) / c) ^ 4 + ((b + c) / d) ^ 4 + ((c + d) / a) ^ 4 + ((d + a) / b) ^ 4) :
    A ≥ 64 := by
        --Introduce variables s, t u and v as follows.
        set s := (a + b) / c
        set t := (b + c) / d
        set u := (c + d) / a
        set v := (d + a) / b
        --Show s ^ 4 + t ^ 4 ≥ 2 * s ^ 2 * t ^ 2.
        have h1 : s ^ 4 + t ^ 4 ≥ 2 * s ^ 2 * t ^ 2 := by
            have : s ^ 4 + t ^ 4 - 2 * s ^ 2 * t ^ 2 ≥ 0 := by
                calc
                    _ = (s ^ 2 - t ^ 2) ^ 2 := by
                        rw [pow_two, pow_two, pow_two, mul_sub]
                        ring
                    _ ≥ 0 := by exact sq_nonneg (s ^ 2 - t ^ 2)
            linarith
        --SHow u ^ 4 + v ^ 4 ≥ 2 * u ^ 2 * v ^ 2.
        have h2 : u ^ 4 + v ^ 4 ≥ 2 * u ^ 2 * v ^ 2 := by
            have : u ^ 4 + v ^ 4 - 2 * u ^ 2 * v ^ 2 ≥ 0 := by
                calc
                    _ = (u ^ 2 - v ^ 2) ^ 2 := by
                        rw [pow_two, pow_two, pow_two, mul_sub]
                        ring
                    _ ≥ 0 := by exact sq_nonneg (u ^ 2 - v ^ 2)
            linarith
        --Show  (s * t) ^ 2 + (u * v) ^ 2 ≥ 2 * (s * t) * (u * v).
        have h3 : (s * t) ^ 2 + (u * v) ^ 2 ≥ 2 * (s * t) * (u * v)  := by
            exact two_mul_le_add_sq (s * t) (u * v)
        --Show s ^ 4 + t ^ 4 + u ^ 4 + v ^ 4 ≥ 2 * (s ^ 2 * t ^ 2 + u ^ 2 * v ^ 2).
        have h4 : s ^ 4 + t ^ 4 + u ^ 4 + v ^ 4 ≥ 2 * (s ^ 2 * t ^ 2 + u ^ 2 * v ^ 2) := by
            linarith
        --Show s ^ 2 * t ^ 2 + u ^ 2 * v ^ 2 ≥ 2 * s * t * u * v .
        have h5 : s ^ 2 * t ^ 2 + u ^ 2 * v ^ 2 ≥ 2 * s * t * u * v := by
            linarith
        --Show s ^ 4 + t ^ 4 + u ^ 4 + v ^ 4 ≥ 4 * (s * t * u * v).
        have h6 : s ^ 4 + t ^ 4 + u ^ 4 + v ^ 4 ≥ 4 * (s * t * u * v) := by
            linarith
        unfold s t u v at h6
        --Show ((a + b) / c) * ((b + c) / d) * ((c + d) / a) * ((d + a) / b) = ((a + b) * (b + c) * (c + d) * (d + a) / (a * b * c * d)).
        have h7 :  ((a + b) / c) * ((b + c) / d) * ((c + d) / a) * ((d + a) / b) = ((a + b) * (b + c) * (c + d) * (d + a) / (a * b * c * d)) := by
            ring
        rw [h7] at h6
        --Show ((a + b) / c) ^ 4 + ((b + c) / d) ^ 4 + ((c + d) / a) ^ 4 + ((d + a) / b) ^ 4 ≥ 64 * ((a + b) * (b + c) * (c + d) * (d + a) / (16 * a * b * c * d)).
        have h8 : ((a + b) / c) ^ 4 + ((b + c) / d) ^ 4 + ((c + d) / a) ^ 4 + ((d + a) / b) ^ 4 ≥ 64 * ((a + b) * (b + c) * (c + d) * (d + a) / (16 * a * b * c * d)) := by
            have h81 : 64 * ((a + b) * (b + c) * (c + d) * (d + a) / (16 * a * b * c * d)) = 4 * (((a + b) * (b + c) * (c + d) * (d + a) / (a * b * c * d))) := by
                field_simp
                ring
            rw [h81]
            exact h6
        --SHow 16 * a * b * c * d = (2 * Real.sqrt (a * b)) * (2 * Real.sqrt (b * c)) * (2 * Real.sqrt (c * d)) * (2 * Real.sqrt (d * a)).
        have h9 :  16 * a * b * c * d = (2 * Real.sqrt (a * b)) * (2 * Real.sqrt (b * c)) * (2 * Real.sqrt (c * d)) * (2 * Real.sqrt (d * a)) := by
            ring_nf
            rw [Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul]
            ring_nf
            rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt ]
            all_goals positivity
        rw [h9] at h8
        --SHow (a + b) / (2 * Real.sqrt (a * b)) ≥ 1.
        have h10 : (a + b) / (2 * Real.sqrt (a * b)) ≥ 1 := by
            have h101 : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := by exact sq_nonneg (√a - √b)
            have h102 : (Real.sqrt a - Real.sqrt b) ^ 2 = (Real.sqrt a)^2 + (Real.sqrt b)^2 - 2 * (Real.sqrt a * Real.sqrt b) := by ring
            have h103 : (Real.sqrt a)^2 = a := by
                refine sq_sqrt ?_
                positivity
            have h104 : (Real.sqrt b)^2 = b := by
                refine sq_sqrt ?_
                positivity
            have h105 : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
                rw [Real.sqrt_mul]
                positivity
            rw [h103, h104, h105] at h102
            rw [h102] at h101
            have h106 : a + b ≥ 2 * Real.sqrt (a * b) := by linarith
            have hdenom_pos : 0 < 2 * √(a * b) := by positivity
            exact (one_le_div₀ hdenom_pos).mpr h106
        --SHow (b + c) / (2 * Real.sqrt (b * c)) ≥ 1.
        have h11 : (b + c) / (2 * Real.sqrt (b * c)) ≥ 1 := by
            have h101 : (Real.sqrt b - Real.sqrt c) ^ 2 ≥ 0 := by exact sq_nonneg (√b - √c)
            have h102 : (Real.sqrt b - Real.sqrt c) ^ 2 = (Real.sqrt b)^2 + (Real.sqrt c)^2 - 2 * (Real.sqrt b * Real.sqrt c) := by ring
            have h103 : (Real.sqrt b)^2 = b := by
                refine sq_sqrt ?_
                positivity
            have h104 : (Real.sqrt c)^2 = c := by
                refine sq_sqrt ?_
                positivity
            have h105 : Real.sqrt b * Real.sqrt c = Real.sqrt (b * c) := by
                rw [Real.sqrt_mul]
                positivity
            rw [h103, h104, h105] at h102
            rw [h102] at h101
            have h106 : b + c ≥ 2 * Real.sqrt (b * c) := by linarith
            have hdenom_pos : 0 < 2 * √(b * c) := by positivity
            exact (one_le_div₀ hdenom_pos).mpr h106
        --Show (c + d) / (2 * Real.sqrt (c * d)) ≥ 1
        have h12 : (c + d) / (2 * Real.sqrt (c * d)) ≥ 1 := by
            have h101 : (Real.sqrt c - Real.sqrt d) ^ 2 ≥ 0 := by exact sq_nonneg (√c - √d)
            have h102 : (Real.sqrt c - Real.sqrt d) ^ 2 = (Real.sqrt c)^2 + (Real.sqrt d)^2 - 2 * (Real.sqrt c * Real.sqrt d) := by ring
            have h103 : (Real.sqrt c)^2 = c := by
                refine sq_sqrt ?_
                positivity
            have h104 : (Real.sqrt d)^2 = d := by
                refine sq_sqrt ?_
                positivity
            have h105 : Real.sqrt c * Real.sqrt d = Real.sqrt (c * d) := by
                rw [Real.sqrt_mul]
                positivity
            rw [h103, h104, h105] at h102
            rw [h102] at h101
            have h106 : c + d ≥ 2 * Real.sqrt (c * d) := by linarith
            have hdenom_pos : 0 < 2 * √(c * d) := by positivity
            exact (one_le_div₀ hdenom_pos).mpr h106
        --Show (d + a) / (2 * Real.sqrt (d * a)) ≥ 1
        have h13 : (d + a) / (2 * Real.sqrt (d * a)) ≥ 1 := by
            have h101 : (Real.sqrt d - Real.sqrt a) ^ 2 ≥ 0 := by exact sq_nonneg (√d - √a)
            have h102 : (Real.sqrt d - Real.sqrt a) ^ 2 = (Real.sqrt d)^2 + (Real.sqrt a)^2 - 2 * (Real.sqrt d * Real.sqrt a) := by ring
            have h103 : (Real.sqrt d)^2 = d := by
                refine sq_sqrt ?_
                positivity
            have h104 : (Real.sqrt a)^2 = a := by
                refine sq_sqrt ?_
                positivity
            have h105 : Real.sqrt d * Real.sqrt a = Real.sqrt (d * a) := by
                rw [Real.sqrt_mul]
                positivity
            rw [h103, h104, h105] at h102
            rw [h102] at h101
            have h106 : d + a ≥ 2 * Real.sqrt (d * a) := by linarith
            have hdenom_pos : 0 < 2 * √(d * a) := by positivity
            exact (one_le_div₀ hdenom_pos).mpr h106
        --SHow ((a + b) * (b + c) * (c + d) * (d + a) / (2 * √(a * b) * (2 * √(b * c)) * (2 * √(c * d)) * (2 * √(d * a)))) = = ((a + b) / (2 * Real.sqrt (a * b))) * ((b + c) / (2 * Real.sqrt (b * c))) * ((c + d) / (2 * Real.sqrt (c * d))) * ((d + a) / (2 * Real.sqrt (d * a))).
        have h14 : ((a + b) * (b + c) * (c + d) * (d + a) / (2 * √(a * b) * (2 * √(b * c)) * (2 * √(c * d)) * (2 * √(d * a))))
            = ((a + b) / (2 * Real.sqrt (a * b))) * ((b + c) / (2 * Real.sqrt (b * c))) * ((c + d) / (2 * Real.sqrt (c * d))) * ((d + a) / (2 * Real.sqrt (d * a))) := by ring
        rw [h14] at h8
        --Show ((a + b) / (2 * Real.sqrt (a * b))) * ((b + c) / (2 * Real.sqrt (b * c))) * ((c + d) / (2 * Real.sqrt (c * d))) * ((d + a) / (2 * Real.sqrt (d * a))) ≥ 1 * 1 * 1 * 1
        have h15 : ((a + b) / (2 * Real.sqrt (a * b))) * ((b + c) / (2 * Real.sqrt (b * c))) * ((c + d) / (2 * Real.sqrt (c * d))) * ((d + a) / (2 * Real.sqrt (d * a))) ≥ 1 * 1 * 1 * 1 := by
            gcongr
        linarith