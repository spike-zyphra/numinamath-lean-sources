import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a b c=\frac{2}{3}$. Prove that

$$
\frac{a b}{a+b}+\frac{b c}{b+c}+\frac{c a}{c+a} \geqslant \frac{a+b+c}{a^{3}+b^{3}+c^{3}}
$$ -/
theorem inequalities_605946 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 2 / 3) :
    (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥
    (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) := by
  -- a ≥ 0, b ≥ 0, c ≥ 0
  have hann : 0 ≤ a := by apply le_of_lt ha
  have hbnn : 0 ≤ b := by apply le_of_lt hb
  have hcnn : 0 ≤ c := by apply le_of_lt hc
  -- Alternative Solution by PSC.
  -- By the Power Mean Inequality we have [ \frac{a^{3}+b^{3}+c^{3}}{3} \geqslant\left(\frac{a+b+c}{3}\right)^{3} ]
  have har : (a ^ 3 + b ^ 3 + c ^ 3) / 3 ≥ ((a + b + c) / 3) ^ 3 := by
    let z (x : ℕ) :=
      match x with
      | 0 => a
      | 1 => b
      | 2 => c
      | _ => 0
    have hzpos : ∀ i ∈ Finset.range 3, 0 ≤ z i := by
      intro i hi
      simp [z]
      match i with
      | 0 => simp [hann]
      | 1 => simp [hbnn]
      | 2 => simp [hcnn]
    -- apply the Power Mean Inequality
    have h := Real.arith_mean_le_rpow_mean (Finset.range 3) (fun x => 1 / 3) z (by simp) (by simp) hzpos (show 1 ≤ 3 by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h
    rw [Finset.sum_range_zero, Finset.sum_range_zero] at h
    simp [z] at h
    -- simplify the inequality
    calc
      (a ^ 3 + b ^ 3 + c ^ 3) / 3 = ((3⁻¹ * a ^ (3 : ℝ) + 3⁻¹ * b ^ (3 : ℝ) + 3⁻¹ * c ^ (3 : ℝ)) ^ (3 : ℝ)⁻¹) ^ (3 : ℝ) := by
        rw [←Real.rpow_mul]
        · simp
          field_simp
          rw [←Real.rpow_natCast, ←Real.rpow_natCast, ←Real.rpow_natCast]
          norm_cast
        · apply add_nonneg
          · apply add_nonneg
            · apply mul_nonneg
              · norm_num
              · apply Real.rpow_nonneg hann
            · apply mul_nonneg
              · norm_num
              · apply Real.rpow_nonneg hbnn
          · apply mul_nonneg
            · norm_num
            · apply Real.rpow_nonneg hcnn
      _ ≥ (3⁻¹ * a + 3⁻¹ * b + 3⁻¹ * c) ^ (3 : ℝ) := by rel [h]
      _ = ((a + b + c) / 3) ^ 3 := by
        rw [←Real.rpow_natCast]
        ring_nf
  -- So it is enough to prove that [ (a+b+c)^{2}\left(\frac{a b}{a+b}+\frac{b c}{b+c}+\frac{c a}{c+a}\right) \geqslant 9 ]
  suffices h : (a + b + c) ^ 2 * (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥ 9
  · calc
      (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥ 9 / (a + b + c) ^ 2 := by
        apply div_le_of_le_mul₀
        · exact sq_nonneg (a + b + c)
        · apply add_nonneg
          · apply add_nonneg
            · apply mul_nonneg
              · apply mul_nonneg hann hbnn
              · simp
                apply add_nonneg hann hbnn
            · apply div_nonneg
              · apply mul_nonneg hbnn hcnn
              · apply add_nonneg hbnn hcnn
          · apply div_nonneg
            · apply mul_nonneg hcnn hann
            · apply add_nonneg hcnn hann
        · rw [mul_comm]
          exact h
      _ ≥ (a + b + c) / (a ^ 3 + b ^ 3 + c ^ 3) := by
        apply div_le_div_iff₀ ?_ ?_ |>.mpr
        · simp [←pow_succ']
          nlinarith [har]
        · apply add_pos
          · apply add_pos
            · apply pow_pos ha
            · apply pow_pos hb
          · apply pow_pos hc
        · apply pow_pos
          apply add_pos
          · apply add_pos ha hb
          · exact hc
  · -- or equivalently, that [ (a+b+c)^{2}\left(\frac{1}{a c+b c}+\frac{1}{b a+c a}+\frac{1}{c b+a b}\right) \geqslant \frac{27}{2} ]
    suffices h' : (a + b + c) ^ 2 * (1 / (a * c + b * c) + 1 / (b * a + c * a) + 1 / (c * b + a * b)) ≥ 27 / 2
    · calc
        (a + b + c) ^ 2 * (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) =
          (a + b + c) ^ 2 * (a * b * c / (a * c + b * c) + b * c * a / (b * a + c * a) + c * a * b / (c * b + a * b)) := by
            congr 2
            · congr 1
              · apply div_eq_div_iff ?_ ?_ |>.mpr
                · ring
                · apply ne_of_gt
                  apply add_pos ha hb
                · apply ne_of_gt
                  apply add_pos
                  · apply mul_pos ha hc
                  · apply mul_pos hb hc
              · apply div_eq_div_iff ?_ ?_ |>.mpr
                · ring
                · apply ne_of_gt
                  apply add_pos hb hc
                · apply ne_of_gt
                  apply add_pos
                  · apply mul_pos hb ha
                  · apply mul_pos hc ha
            · apply div_eq_div_iff ?_ ?_ |>.mpr
              · ring
              · apply ne_of_gt
                apply add_pos hc ha
              · apply ne_of_gt
                apply add_pos
                · apply mul_pos hc hb
                · apply mul_pos ha hb
        _ = (a + b + c) ^ 2 * ((2 / 3) / (a * c + b * c) + (2 / 3) / (b * a + c * a) + (2 / 3) / (c * b + a * b)) := by
          congr 3
          · simp [habc]
          · congr 1
            rw [mul_comm, ←mul_assoc, habc]
          · rw [mul_assoc, mul_comm, habc]
        _ = (a + b + c) ^ 2 * (1 / (a * c + b * c) + 1 / (b * a + c * a) + 1 / (c * b + a * b)) * (2 / 3) := by ring
        _ ≥ 27 / 2 * (2 / 3) := by rel [h']
        _ = 9 := by norm_num
    · -- prove AGM inequality
      have ag2 {x y : ℝ} (hx : x ≥ 0) (hy : y ≥ 0) : (x + y) / 2 ≥ √(x * y) := by
        let z (n : ℕ) :=
          match n with
          | 0 => x
          | 1 => y
          | _ => 0
        have hz : ∀ i ∈ Finset.range 2, 0 ≤ z i := by
          intro i hi
          simp [z]
          match i with
          | 0 => exact hx
          | 1 => exact hy
        have h := Real.geom_mean_le_arith_mean (Finset.range 2) (fun x => 1 / 2) z (by simp) (by simp) hz
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero] at h
        rw [Finset.sum_range_zero, Finset.sum_range_zero] at h
        simp [z] at h
        norm_num at h
        calc
          (x + y) / 2 = 1 / 2 * x + 1 / 2 * y := by ring
          _ ≥ x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) := by rel [h]
          _ = √(x * y) := by rw [Real.sqrt_eq_rpow, Real.mul_rpow hx hy]
      -- prove a ^ 2 + b ^ 2 + c ^ 2 ≥ a b + b c + c a
      have hsqsum : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
        calc
          a ^ 2 + b ^ 2 + c ^ 2 = (a ^ 2 + b ^ 2) / 2 + (b ^ 2 + c ^ 2) / 2 + (c ^ 2 + a ^ 2) / 2 := by ring
          _ ≥ √(a ^ 2 * b ^ 2) + √(b ^ 2 * c ^ 2) + √(c ^ 2 * a ^ 2) := by
            apply add_le_add
            · apply add_le_add
              · exact ag2 (sq_nonneg a) (sq_nonneg b)
              · exact ag2 (sq_nonneg b) (sq_nonneg c)
            · exact ag2 (sq_nonneg c) (sq_nonneg a)
          _ = a * b + b * c + c * a := by
            rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq hann, Real.sqrt_sq hbnn]
            rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hbnn, Real.sqrt_sq hcnn]
            rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hcnn, Real.sqrt_sq hann]
      -- Since ((a+b+c)^{2} \geqslant 3(a b+b c+c a)=\frac{3}{2}((a c+b c)+(b a+c a)+(c b+a c)))\
      have h'' : (a + b + c) ^ 2 ≥ 3 / 2 * ((a * c + b * c) + (b * a + c * a) + (c * b + a * b)) := by
        calc
          (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by ring
          _ ≥ a * b + b * c + c * a + 2 * (a * b + b * c + c * a) := by
            apply add_le_add_right
            exact hsqsum
          _ = 3 / 2 * ((a * c + b * c) + (b * a + c * a) + (c * b + a * b)) := by ring
      -- prove the cauchy inequality
      have cauchy {a b c x y z : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) :
          (√(a * x) + √(b * y) + √(c * z)) ^ 2 ≤ (a + b + c) * (x + y + z) := by
        let f (n : ℕ) :=
          match n with
          | 0 => a
          | 1 => b
          | 2 => c
          | _ => 0
        let g (n : ℕ) :=
          match n with
          | 0 => x
          | 1 => y
          | 2 => z
          | _ => 0
        have hf (i : ℕ) : 0 ≤ f i := by
          simp [f]
          match i with
          | 0 => exact ha
          | 1 => exact hb
          | 2 => exact hc
          | k + 3 => simp
        have hg (i : ℕ) : 0 ≤ g i := by
          simp [g]
          match i with
          | 0 => exact hx
          | 1 => exact hy
          | 2 => exact hz
          | k + 3 => simp
        have h := Real.sum_sqrt_mul_sqrt_le (Finset.range 3) hf hg
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h
        rw [Finset.sum_range_zero, Finset.sum_range_zero] at h
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
        simp [f, g] at h
        calc
          (√(a * x) + √(b * y) + √(c * z)) ^ 2 = (√a * √x + √b * √y + √c * √z) ^ 2 := by
            rw [Real.sqrt_mul ha, Real.sqrt_mul hb, Real.sqrt_mul hc]
          _ ≤ (√(a + b + c) * √(x + y + z)) ^ 2 := by rel [h]
          _ = (a + b + c) * (x + y + z) := by
            have : a + b + c ≥ 0 := by
              apply add_nonneg
              · apply add_nonneg
                · exact ha
                · exact hb
              · exact hc
            rw [←Real.sqrt_mul this, Real.sq_sqrt]
            · apply mul_nonneg
              · exact this
              · apply add_nonneg
                · apply add_nonneg
                  · exact hx
                  · exact hy
                · exact hz
      -- then (5) follows by the Cauchy-Schwarz Inequality.
      calc
        (a + b + c) ^ 2 * (1 / (a * c + b * c) + 1 / (b * a + c * a) + 1 / (c * b + a * b)) ≥
          3 / 2 * ((a * c + b * c) + (b * a + c * a) + (c * b + a * b)) * (1 / (a * c + b * c) + 1 / (b * a + c * a) + 1 / (c * b + a * b)) := by rel [h'']
        _ = 3 / 2 * (((a * c + b * c) + (b * a + c * a) + (c * b + a * b)) * (1 / (a * c + b * c) + 1 / (b * a + c * a) + 1 / (c * b + a * b))) := by ring
        _ ≥ 3 / 2 * (√ ((a * c + b * c) * (1 / (a * c + b * c))) + √ ((b * a + c * a) * (1 / (b * a + c * a))) + √ ((c * b + a * b) * (1 / (c * b + a * b))) ) ^ 2 := by
          have h1 : a * c + b * c ≥ 0 := by
            apply add_nonneg
            · apply mul_nonneg hann hcnn
            · apply mul_nonneg hbnn hcnn
          have h2 : b * a + c * a ≥ 0 := by
            apply add_nonneg
            · apply mul_nonneg hbnn hann
            · apply mul_nonneg hcnn hann
          have h3 : c * b + a * b ≥ 0 := by
            apply add_nonneg
            · apply mul_nonneg hcnn hbnn
            · apply mul_nonneg hann hbnn
          apply mul_le_mul_of_nonneg_left
          · apply cauchy h1 h2 h3
            · apply div_nonneg
              · norm_num
              · exact h1
            · apply div_nonneg
              · norm_num
              · exact h2
            · apply div_nonneg
              · norm_num
              · exact h3
          · norm_num
        _ = 3 / 2 * (1 + 1 + 1) ^ 2 := by
          rw [mul_div_cancel₀, mul_div_cancel₀, mul_div_cancel₀]
          · norm_num
          · apply ne_of_gt
            apply add_pos
            · apply mul_pos hc hb
            · apply mul_pos ha hb
          · apply ne_of_gt
            apply add_pos
            · apply mul_pos hb ha
            · apply mul_pos hc ha
          · apply ne_of_gt
            apply add_pos
            · apply mul_pos ha hc
            · apply mul_pos hb hc
        _ = 27 / 2 := by norm_num
