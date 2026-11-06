import Mathlib

open Real

/- The positive reals $ x,y$ and $ z$ are satisfying the relation $ x \plus{} y \plus{} z\geq 1$. Prove that:
$ \frac {x\sqrt {x}}{y \plus{} z} \plus{} \frac {y\sqrt {y}}{z \plus{} x} \plus{} \frac {z\sqrt {z}}{x \plus{} y}\geq \frac {\sqrt {3}}{2}$

[i]Proposer[/i]:[b] Baltag Valeriu[/b] -/
theorem inequalities_55101 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ 1) :
    sqrt 3 / 2 ≤ x * sqrt x / (y + z) + y * sqrt y / (z + x) + z * sqrt z / (x + y) := by
  -- It is easy to prove by AM-GM that:\
  -- $ \frac{x}{y+z}\geq \frac{3}{2}\cdot \frac{x^{\frac{3}{2}}}{x^{\frac{3}{2}}+y^{\frac{3}{2}}+z^{\frac{3}{2}}}$ , etc,\
  have ham_gm {x y : ℝ} (hx : x > 0) (hy : y > 0) : x ^ (1 / 2 : ℝ) * y ≤ (x ^ (3 / 2 : ℝ) + 2 * y ^ (3 / 2 : ℝ)) / 3 := by
    obtain h := geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3) (by simp) (by simp) (by simp) (p₁ := x ^ (3 / 2 : ℝ)) (rpow_nonneg (le_of_lt hx) _) (p₂ := y ^ (3 / 2 : ℝ)) (rpow_nonneg (le_of_lt hy) _) (p₃ := y ^ (3 / 2 : ℝ)) (rpow_nonneg (le_of_lt hy) _) (by norm_num)
    trans (x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) * (y ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) * (y ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)
    · apply le_of_eq
      rw [←rpow_mul (le_of_lt hx), ←rpow_mul (le_of_lt hy)]
      norm_num
      rw [←sqrt_eq_rpow, ←sqrt_eq_rpow, mul_assoc, mul_self_sqrt (le_of_lt hy)]
    · apply le_trans h
      apply le_of_eq
      field_simp
      ring
  have {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x / (y + z) ≥ 3 / 2 * (x ^ (3 / 2 : ℝ) / (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ))) := by
    trans x ^ (3 / 2 : ℝ) / (x ^ (1 / 2 : ℝ) * y + x ^ (1 / 2 : ℝ) * z)
    · apply le_of_eq
      field_simp
      rw [show 3 / 2 = 1 / 2 + (1 : ℝ) by norm_num, rpow_add hx, rpow_one]
      ring
    · trans x ^ (3 / 2 : ℝ) / ((x ^ (3 / 2 : ℝ) + 2 * y ^ (3 / 2 : ℝ)) / 3 + (x ^ (3 / 2 : ℝ) + 2 * z^ (3 / 2 : ℝ)) / 3)
      · rel [ham_gm hx hy, ham_gm hx hz]
      · apply le_of_eq
        field_simp
        ring
  -- So it suffices to show that:\
  -- ${ \sum{\frac{x^2}{x^{\frac{3}{2}}+y^{\frac{3}{2}}+z^{\frac{3}{2}}}}\geq \frac{1}{\sqrt{3}}
  suffices h : (x ^ 2 + y ^ 2 + z ^ 2) / (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ)) ≥ 1 / √3
  · trans 3 / 2 * (1 / √3)
    · apply le_of_eq
      field_simp
      ring_nf
      norm_num
    · trans 3 / 2 * ((x ^ 2 + y ^ 2 + z ^ 2) / (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ)))
      · rel [h]
      · trans 3 / 2 * (x ^ (3 / 2 : ℝ) / (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ))) * x ^ (1 / 2 : ℝ) + 3 / 2 * (y ^ (3 / 2 : ℝ) / (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ))) * y ^ (1 / 2 : ℝ) + 3 / 2 * (z ^ (3 / 2 : ℝ) / (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ))) * z ^ (1 / 2 : ℝ)
        · apply le_of_eq
          field_simp
          rw [mul_assoc, mul_assoc, mul_assoc, ←rpow_add hx, ←rpow_add hy, ←rpow_add hz]
          norm_num
          rw [mul_add, mul_add]
        · trans  3 / 2 * (x ^ (3 / 2 : ℝ) / (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ))) * x ^ (1 / 2 : ℝ) + 3 / 2 * (y ^ (3 / 2 : ℝ) / (y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ))) * y ^ (1 / 2 : ℝ) + 3 / 2 * (z ^ (3 / 2 : ℝ) / (z ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ))) * z ^ (1 / 2 : ℝ)
          · apply le_of_eq
            ring
          · trans x / (y + z) * x ^ (1 / 2 : ℝ) + y / (z + x) * y ^ (1 / 2 : ℝ) + z / (x + y) * z ^ (1 / 2 : ℝ)
            · rel [this hx hy hz, this hy hz hx, this hz hx hy]
            · apply le_of_eq
              rw [sqrt_eq_rpow, sqrt_eq_rpow, sqrt_eq_rpow]
              ring
  · -- \iff 3(x^2+y^2+z^2)^2\geq (x^{\frac{3}{2}}+y^{\frac{3}{2}}+z^{\frac{3}{2}}})^2$\
    suffices h : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 ≥ (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ)) ^ 2
    · apply div_le_div_iff₀ ?_ ?_ |>.mpr
      · rw [one_mul]
        apply pow_le_pow_iff_left₀ (n := 2) ?_  ?_ (by simp) |>.mp
        · rw [mul_pow, sq_sqrt (by simp), mul_comm]
          exact h
        all_goals positivity
      all_goals positivity
    ·  -- It suffices to show that:
      -- ${ 3(x^2+y^2+z^2)^2(x+y+z)\geq (x+y+z)(x^{\frac{3}{2}}+y^{\frac{3}{2}}+z^{\frac{3}{2}}})^2$
      suffices h : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 * (x + y + z) ≥ (x + y + z) * (x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ)) ^ 2
      · apply le_of_mul_le_mul_right (a := (x + y + z))
        · apply le_trans ?_ h
          apply le_of_eq
          ring
        · positivity
      · -- By CS we get that:
        -- ${ (x^2+y^2+z^2)(x+y+z)\geq (x^{\frac{3}{2}}+y^{\frac{3}{2}}+z^{\frac{3}{2}}})^2$ 
        let f (i : Fin 3) := 
          match i with
          | 0 => x ^ 2
          | 1 => y ^ 2
          | 2 => z ^ 2
        let g (i : Fin 3) := 
          match i with
          | 0 => x
          | 1 => y
          | 2 => z
        let r (i : Fin 3) := 
          match i with
          | 0 => x ^ (3 / 2 : ℝ)
          | 1 => y ^ (3 / 2 : ℝ)
          | 2 => z ^ (3 / 2 : ℝ)
        have hf : ∀ i ∈ Finset.univ, 0 ≤ f i := by 
          intro i _; 
          fin_cases i <;> (simp [f]; positivity)
        have hg : ∀ i ∈ Finset.univ, 0 ≤ g i := by
          intro i _; 
          fin_cases i <;> (simp [g]; positivity)
        have hr : ∀ i ∈ Finset.univ, r i ^ 2 = f i * g i := by
          intro i _; 
          fin_cases i
          all_goals
            simp [f, g, r]
            rw [show 3 / 2 = 1 / 2 + (1 : ℝ) by norm_num, rpow_add, rpow_one]
            rw [mul_pow, ←sqrt_eq_rpow, sq_sqrt, mul_comm]
            all_goals positivity
        have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ hf hg hr
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at h
        simp [f, g, r, ←add_assoc] at h
        -- and $ 3(x^2+y^2+z^2)\geq (x+y+z)^2\geq (x+y+z)$ , so we are done.
        trans 3 * (x ^ 2 + y ^ 2 + z ^ 2) * ((x ^ 2 + y ^ 2 + z ^ 2) * (x + y + z))
        · apply le_of_eq
          ring
        · trans 3 * (x ^ 2 + y ^ 2 + z ^ 2) * ((x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ)) ^ 2)
          · rel [h]
          · gcongr
            trans (x + y + z) ^ 2
            · apply le_self_pow₀
              assumption
              simp
            · let g (i : Fin 3) := 
                match i with
                | 0 => x
                | 1 => y
                | 2 => z
              obtain h := sq_sum_le_card_mul_sum_sq (f := g) (s := Finset.univ)
              simp [Fin.sum_univ_succ, Fin.sum_univ_succ, g, ←add_assoc] at h
              exact h

