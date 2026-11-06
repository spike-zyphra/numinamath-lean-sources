import Mathlib

open Real

set_option maxHeartbeats 0

/- Let $x,$ $y,$ $z$ be positive real numbers.  Find the minimum value of
\[\frac{(1 + 5z)(4z + 3x)(5x + 6y)(y + 18)}{xyz}.\] -/
theorem algebra_20447{f: ℝ → ℝ → ℝ → ℝ}(hf: f = fun x y z => (1 + 5 * z) * (4 * z + 3 * x) * (5 * x + 6 * y) * (y + 18) / (x * y * z)):
  IsLeast {u:ℝ | ∃(x y z : ℝ), u = f x y z ∧ 0 < x ∧ 0 < y ∧ 0 < z}
  5120 := by
  rw [IsLeast, lowerBounds]; simp
  constructor
  -- we will show the inequality using AM-GM, and by using AM-GM, we know the condition that equal sign holds. in the first direction, we just verify the equality using corresponding values, specific proof is at the second direction.
  · use 12/5; use 6; use 3/5
    rw [hf]; simp
    ring
  · intro u x y z hu posx posy posz
    -- simplify the expression
    have h1: u = (32/135) *
      (((1+5*z)*(5*z+(15/4)*x)*((15/4)*x+(9/2)*y)*((9/2)*y+81))
      /(x*y*z)) := by
      rw [hu, hf]; simp
      ring
    -- let a = 5z, b = 15/4x, c = 9/2y
    let a := 5*z
    have a_def: a = 5*z := rfl
    have posa: 0 < a := by
      rw [a_def]; linarith [posz]
    let b := (15/4)*x
    have b_def: b = (15/4)*x := rfl
    have posb: 0 < b := by
      rw [b_def]; linarith [posx]
    let c := (9/2)*y
    have c_def: c = (9/2)*y := rfl
    have posc: 0 < c := by
      rw [c_def]; linarith [posy]
    -- therefore u simplifies to 20 (1+a)(1+b/a)(1+c/b)(1+81/c)
    have h2: u = 20*(1+a)*(1+b/a)*(1+c/b)*(1+81/c) := by
      rw [h1, ← a_def, ← b_def, ← c_def]
      have: x*y*z = a*b*c * 8/675 := by
        rw [a_def, b_def, c_def]; ring
      rw [this]; field_simp; ring
    -- we can use AM-GM to simplify
    have AM_GM1(m n : ℝ)(mpos: 0 < m)(npos: 0 < n):
      m + 3/4*n ≥ 4 *(m*((n/4)^(3:ℝ)))^(1/4:ℝ) := by
      have hh3: 0 ≤ (1/4:ℝ) := by norm_num
      have hh4: 0 ≤ m := le_of_lt mpos
      have hh5: 0 ≤ (1/4)*n := by linarith [hh3, npos]
      have hh6 := geom_mean_le_arith_mean4_weighted hh3 hh3 hh3 hh3
        hh4 hh5 hh5 hh5 (by norm_num)
      have hh7:  m ^ (1 / 4:ℝ) * (1 / 4 * n) ^ (1 / 4 : ℝ) * (1 / 4 * n) ^ (1 / 4:ℝ) * (1 / 4 * n) ^ (1 / 4:ℝ) = (m*(n/4)^(3:ℝ))^(1/4:ℝ) := by
        field_simp
        ring_nf
        have tt1: ((n * (1 / 4)) ^ (1 / 4:ℝ))^(3:ℝ) = ((n*(1/4))^(3:ℝ))^(1/4:ℝ) := by
          rw [← rpow_mul, ← rpow_mul]
          have: (1/4:ℝ)*3 = 3*(1/4) := by ring
          rw [this]
          linarith [npos]
          linarith [npos]
        have tt2: (n*(1/4))^(3:ℝ) = n^(3:ℝ)/64 := by
          have: (3:ℝ) = 2+1 := by ring
          rw [this, rpow_add, rpow_add, rpow_two, rpow_two];
          field_simp
          ring
          linarith [npos]
          linarith [npos]
        have tt3: ((n * (1 / 4)) ^ (1 / 4:ℝ))^(3:ℝ) =
          ((n * (1 / 4)) ^ (1 / 4:ℝ))^(3:ℕ) := by
          by_cases ht:  ((n * (1 / 4)) ^ (1 / 4:ℝ)) = 0
          · rw [ht]; simp
          · push_neg at ht
            have: (3:ℝ) = 2+1 := by ring
            rw [this, rpow_add_one ht, rpow_two]; ring
        rw [tt3] at tt1
        rw [tt1, tt2]
        rw [mul_rpow]
        linarith [mpos]
        have: 0 ≤ n^(3:ℝ) := by
          have hh2: 0 ≤ n := le_of_lt npos
          exact rpow_nonneg hh2 3
        linarith [this]
      have hh8: 1 / 4 * m + 1 / 4 * (1 / 4 * n) + 1 / 4 * (1 / 4 * n) + 1 / 4 * (1 / 4 * n) = (m+3/4 * n)/4 := by ring
      rw [hh7, hh8] at hh6
      have hh9: 0 < (4:ℝ) := by norm_num
      rw [mul_comm 4]
      apply (le_div_iff₀ hh9).mp hh6
    -- 1+a = 1 + 3/4 * (4/3*a)
    have h3: 1+a ≥ 4*((a/3)^(3:ℝ))^(1/4:ℝ) := by
      have hh1: 1+a = 1 + 3/4 * (4/3 * a) := by ring
      have hh2 := AM_GM1 1 (4/3*a) (by norm_num) (by linarith [posa])
      have hh3: 1*(4/3*a/4)^(3:ℝ) = (a/3)^(3:ℝ) := by
        have: 4/3*a/4 = a/3 := by ring
        rw [this]; simp
      rw [hh1, ← hh3]
      apply hh2
    -- 1+b/a = 1+3/4 * (4/3*(b/a))
    have h4: 1+b/a ≥ 4*((b/(3*a))^(3:ℝ))^(1/4:ℝ) := by
      have hh1: b/a = 3/4 * (4/3 *(b/a)) := by ring
      have hh2: 0 < 4/3 * (b/a) := by
        have: 0 < b/a := by
          exact div_pos posb posa
        linarith [this]
      have hh3 := AM_GM1 1 (4/3*(b/a)) (by norm_num) hh2
      rw [hh1]
      have hh4: (b / (3 * a))^(3:ℝ) = 1*((4/3*(b/a)/4))^(3:ℝ) := by
        have: 4/3 * (b/a)/4 = b/(3*a) := by ring
        rw [this]; simp
      rw [hh4]
      apply hh3
    -- 1+c/b
    have h5: 1+c/b ≥ 4*((c/(3*b))^(3:ℝ))^(1/4:ℝ) := by
      have hh1: c/b = 3/4 * (4/3 *(c/b)) := by ring
      have hh2: 0 < 4/3 * (c/b) := by
        have: 0 < c/b := by
          exact div_pos posc posb
        linarith [this]
      have hh3 := AM_GM1 1 (4/3*(c/b)) (by norm_num) hh2
      rw [hh1]
      have hh4: (c / (3 * b))^(3:ℝ) = 1*((4/3*(c/b)/4))^(3:ℝ) := by
        have: 4/3 * (c/b)/4 = c/(3*b) := by ring
        rw [this]; simp
      rw [hh4]
      apply hh3
    have h6: 1+81/c ≥ 4*((27/c)^(3:ℝ))^(1/4:ℝ) := by
      have hh1: 81/c = 3/4 * (4/3 *(81/c)) := by ring
      have hh2: 0 < 4/3 * (81/c) := by
        have: 0 < 81/c := by
          exact div_pos (by norm_num) posc
        linarith [this]
      have hh3 := AM_GM1 1 (4/3*(81/c)) (by norm_num) hh2
      rw [hh1]
      have hh4: (27/c)^(3:ℝ) = 1*((4/3*(81/c)/4))^(3:ℝ) := by
        have: 4/3 * (81/c)/4 = 27/c := by ring
        rw [this]; simp
      rw [hh4]
      apply hh3
    -- so u ≥ their product.equal sign takes when a/3 = b/(3a) = c/(3b) = 27/c = 1.
    have h7: u ≥ 20 * (4*((a/3)^(3:ℝ))^(1/4:ℝ)) * (4*((b/(3*a))^(3:ℝ))^(1/4:ℝ)) * (4*((c/(3*b))^(3:ℝ))^(1/4:ℝ)) * (4*((27/c)^(3:ℝ))^(1/4:ℝ))
      := by
      rw [h2]
      have hba: 0 < b/a := div_pos posb posa
      have hcb: 0 < c/b := div_pos posc posb
      have hht1: 0 < ((27 / c) ^ (3:ℝ)) ^ (1 / 4:ℝ) := by
          have hh1: 0 < 27/c := by
            apply div_pos (by norm_num) posc
          have hh2: 0 < (27/c)^(3:ℝ) := by
            exact rpow_pos_of_pos hh1 3
          exact rpow_pos_of_pos hh2 (1 / 4)
      have hh1: 20*(1+a)*(1+b/a)*(1+c/b)*(1+81/c) ≥
        20*(1+a)*(1+b/a)*(1+c/b) * (4*((27/c)^(3:ℝ))^(1/4:ℝ)) := by
        apply mul_le_mul (le_refl _) h6
        linarith [hht1]
        apply le_of_lt
        apply mul_pos
        apply mul_pos
        linarith [posa]
        linarith [hba]
        linarith [hcb]
      apply le_trans ?_ hh1
      apply mul_le_mul ?_ (le_refl _) (by linarith [hht1])
      · apply le_of_lt
        apply mul_pos
        apply mul_pos (by linarith [posa]) (by linarith [hba])
        linarith [hcb]
      have hht2: 0 < 4*((c/(3*b))^(3:ℝ))^(1/4:ℝ) := by
        have tt1: 0 < (c/(3*b))^(3:ℝ) := by
          apply rpow_pos_of_pos
          apply div_pos posc (by linarith [posb])
        have tt2: 0 < ((c/(3*b))^(3:ℝ))^(1/4:ℝ) := by
          apply rpow_pos_of_pos tt1
        linarith [tt2]
      have hh2: 20*(1+a)*(1+b/a)*(1+c/b) ≥ 20*(1+a)*(1+b/a)
        * (4*((c/(3*b))^(3:ℝ))^(1/4:ℝ)) := by
        apply mul_le_mul (le_refl _) h5 (le_of_lt hht2)
        · apply le_of_lt
          apply mul_pos (by linarith [posa])
          linarith [hba]
      apply le_trans ?_ hh2
      apply mul_le_mul ?_ (le_refl _) (le_of_lt hht2)
      · apply le_of_lt
        apply mul_pos (by linarith [posa])
        linarith [hba]
      have hht3: 0 < 4*((b/(3*a))^(3:ℝ))^(1/4:ℝ) := by
        have: 0 < ((b/(3*a))^(3:ℝ))^(1/4:ℝ) := by
          apply rpow_pos_of_pos
          apply rpow_pos_of_pos
          apply div_pos posb (by linarith [posa])
        linarith [this]
      have hh3: 20*(1+a)*(1+b/a) ≥ 20 * (1+a) *
        (4*((b/(3*a))^(3:ℝ))^(1/4:ℝ)) := by
        apply mul_le_mul (le_refl _) h4 (le_of_lt hht3)
        linarith [posa]
      apply le_trans ?_ hh3
      apply mul_le_mul (by linarith [h3]) (le_refl _) (le_of_lt hht3)
      linarith [posa]
    -- simplify
    have h8:  20 * (4*((a/3)^(3:ℝ))^(1/4:ℝ)) * (4*((b/(3*a))^(3:ℝ))^(1/4:ℝ)) * (4*((c/(3*b))^(3:ℝ))^(1/4:ℝ)) * (4*((27/c)^(3:ℝ))^(1/4:ℝ))
    = 5120 * ((a/3)^3 * (b/(3*a))^3 * (c/(3*b))^3 * ((27/c))^3)^(1/4:ℝ) := by
      have hpow3(x:ℝ)(hx: 0 < x):x^(3:ℝ) = x^3 := by
        have: (3:ℝ) = 2+1 := by ring
        rw [this, rpow_add hx, rpow_two]; simp; ring
      have hh1:  20 * (4*((a/3)^(3:ℝ))^(1/4:ℝ)) * (4*((b/(3*a))^(3:ℝ))^(1/4:ℝ)) * (4*((c/(3*b))^(3:ℝ))^(1/4:ℝ)) * (4*((27/c)^(3:ℝ))^(1/4:ℝ))
        = (20*4*4*4*4) * ((a/3)^(3:ℝ))^(1/4:ℝ) * ((b/(3*a))^(3:ℝ))^(1/4:ℝ) * ((c/(3*b))^(3:ℝ))^(1/4:ℝ) * ((27/c)^(3:ℝ))^(1/4:ℝ) := by ring
      have hh2: (20*4*4*4*4) * ((a/3)^(3:ℝ))^(1/4:ℝ) * ((b/(3*a))^(3:ℝ))^(1/4:ℝ) * ((c/(3*b))^(3:ℝ))^(1/4:ℝ) * ((27/c)^(3:ℝ))^(1/4:ℝ) =
        5120 *( (((a/3)^(3:ℝ))^(1/4:ℝ) * ((b/(3*a))^(3:ℝ))^(1/4:ℝ)) *
        (((c/(3*b))^(3:ℝ))^(1/4:ℝ) * ((27/c)^(3:ℝ))^(1/4:ℝ))) := by ring
      rw [hh1, hh2]
      have hh3: ((a/3)^(3:ℝ))^(1/4:ℝ) * ((b/(3*a))^(3:ℝ))^(1/4:ℝ) =
        ((a/3)^3 * (b/(3*a))^3)^(1/4:ℝ) := by
        rw [mul_rpow, hpow3 _, hpow3 _]
        · apply div_pos posb (by linarith [posa])
        · linarith [posa]
        · apply le_of_lt
          apply pow_pos (by linarith [posa])
        · apply le_of_lt
          apply pow_pos
          apply div_pos posb (by linarith [posa])
      have hh4: ((c/(3*b))^(3:ℝ))^(1/4:ℝ) * ((27/c)^(3:ℝ))^(1/4:ℝ) =
        ((c/(3*b))^3 * (27/c)^3)^(1/4:ℝ) := by
        have tt1: 0 < (27/c) := by
          apply div_pos (by norm_num) posc
        have tt2: 0 < c/(3*b) := by
          apply div_pos posc (by linarith [posb])
        rw [hpow3 _ tt1, hpow3 _ tt2]
        rw [mul_rpow]
        · apply le_of_lt
          apply pow_pos tt2
        · apply le_of_lt
          apply pow_pos tt1
      rw [hh3, hh4]
      have hh5: ((a/3)^3 * (b/(3*a))^3)^(1/4:ℝ) * ((c/(3*b))^3 * (27/c)^3)^(1/4:ℝ) = ( (a/3)^3 * (b/(3*a))^3 * ((c/(3*b))^3 * (27/c)^3))^(1/4:ℝ) := by
        rw [← mul_rpow]
        · have tt1: 0 < (a/3)^3 := by
            apply pow_pos (div_pos posa (by norm_num))
          have tt2: 0 < (b/(3*a))^3 := by
            apply pow_pos
            apply div_pos posb (by linarith [posa])
          apply le_of_lt
          apply mul_pos tt1 tt2
        · apply le_of_lt
          apply mul_pos
          · apply pow_pos
            apply div_pos posc (by linarith [posb])
          · apply pow_pos
            apply div_pos (by norm_num) posc
      rw [hh5]
      ring_nf
    --simplify
    have h9: ((a/3)^3 * (b/(3*a))^3 * (c/(3*b))^3 * ((27/c))^3) = 1 := by
      have hh1: ((a/3)^3 * (b/(3*a))^3 * (c/(3*b))^3 * ((27/c))^3) =
        ((a/3) * (b/(3*a)) * (c/(3*b)) * (27/c))^3 := by ring
      have hh2: (a/3) * (b/(3*a)) * (c/(3*b)) * (27/c) = 1 := by
        field_simp; ring
      rw [hh1, hh2]; simp
    rw [h8, h9] at h7; simp at h7
    apply h7
