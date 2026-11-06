import Mathlib

theorem inequalities_126189 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c := by
  have ha : a ≥ 0 := le_of_lt ha
  have hb : b ≥ 0 := le_of_lt hb
  have hc : c ≥ 0 := le_of_lt hc
  -- On applique l'IAG à chaque terme du produit :
  -- cela donne $a+b \geqslant 2 \sqrt{a b}, b+c \geqslant 2 \sqrt{b c}$ et $c+a \geqslant 2 \sqrt{c a}$.
  have h {a b : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) : a + b ≥ 2 * Real.sqrt (a * b) := by
    obtain h := @Real.geom_mean_le_arith_mean2_weighted (1 / 2) (1 / 2) a b (by simp) (by simp) ha hb (by norm_num)
    trans 2 * (1 / 2 * a + 1 / 2 * b)
    · apply le_of_eq; ring
    · apply mul_le_mul (by simp)
      · apply le_of_eq_of_le ?_ h
        rw [Real.sqrt_eq_rpow, Real.mul_rpow ha hb]
      · exact Real.sqrt_nonneg (a * b)
      · norm_num

  -- Comme tout est positif, on peut faire le produit de ces trois inégalités,
  -- ce qui nous donne $(a+b)(b+c)(c+a) \geqslant 8 \sqrt{a b} \sqrt{b c} \sqrt{c a}=8 \sqrt{a^{2} b^{2} c^{2}}=8 a b c$ comme voulu.
  calc
    _ ≥ (2 * Real.sqrt (a * b)) * (2 * Real.sqrt (b * c)) * (2 * Real.sqrt (c * a)) := by rel [h ha hb, h hb hc, h hc ha]
    _ = _ := by
      rw [Real.sqrt_mul ha, Real.sqrt_mul hb, Real.sqrt_mul hc]
      ring_nf
      rw [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc]
