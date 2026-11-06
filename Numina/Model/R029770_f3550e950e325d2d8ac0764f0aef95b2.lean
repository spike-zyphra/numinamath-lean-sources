import Mathlib

theorem algebra_209777 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ∃ r, b = a * r ∧ c = b * r) :
    ∃ r, √(3 * (a * b + b * c + c * a)) = r * (a + b + c) ∧
    (27 * a * b * c) ^ ((1 : ℝ) / 3) = r * √(3 * (a * b + b * c + c * a)) := by 
  rcases h with ⟨r, hb1, hc1⟩
  have hc2 : c = a * r ^ 2 := by 
    rw [hc1, hb1]
    ring
  have hr1 : 0 < r := by 
    nlinarith [hb1, ha, hb, hc2, hc]
  have eq1 : 27 * a * b * c = (3 * a * r) ^ 3 := by
    rw [show b = a * r by linarith [hb1], show c = a * r ^ 2 by linarith [hc1, hb1]]
    ring
  have h1 : (27 * a * b * c) ^ ((1 : ℝ) / 3) = 3 * a * r := by
    rw [eq1]
    have h2 : ((3 * a * r : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (3 * a * r : ℝ) := by
      have h3 : ((3 * a * r : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (3 * a * r : ℝ) := by 
        rw [←Real.rpow_natCast, ←Real.rpow_mul]
        norm_num 
        all_goals 
          nlinarith [ha, hr1]
      linarith
    linarith
  use (√(3 * (a * b + b * c + c * a)) / (a + b + c))
  constructor
  · -- First, prove that $\sqrt{3 * (a * b + b * c + c * a)} = r * (a + b + c)$
    have hne1 : a + b + c > 0 := by
      nlinarith [ha, hb, hc, hb1, hc1]
    field_simp [hne1]
    <;> nlinarith
  · -- Now, prove that $(27 * a * b * c) ^ (1 / 3) = r * \sqrt{3 * (a * b + b * c + c * a)}$
    rw [h1]
    have hne1 : a + b + c > 0 := by
      nlinarith [ha, hb, hc, hb1, hc1]
    have h5 : √(3 * (a * b + b * c + c * a)) > 0 := by
      apply Real.sqrt_pos.mpr 
      nlinarith [show 0 < a * b + b * c + c * a by positivity, ha, hb, hc, hb1, hc1]
    have h6 : (√(3 * (a * b + b * c + c * a)) / (a + b + c)) * √(3 * (a * b + b * c + c * a)) =  √(3 * (a * b + b * c + c * a)) ^ 2 / (a + b + c) := by 
      field_simp [hne1, h5]
      <;> nlinarith [Real.sqrt_nonneg (3 * (a * b + b * c + c * a))]
    have h7 : √(3 * (a * b + b * c + c * a)) ^ 2 = 3 * (a * b + b * c + c * a) := by
      rw [Real.sq_sqrt]
      nlinarith [ha, hb, hc, hb1, hc1]
    rw [h6, h7]
    have h8 : (3 * (a * b + b * c + c * a)) / (a + b + c) = 3 * a * r := by
      rw [show b = a * r by linarith [hb1], show c = a * r ^ 2 by linarith [hc1, hb1]]
      field_simp [hr1, ha] -- Use hr1 for positivity of r and ha for positivity of a
      <;> ring_nf 
    rw [h8]
    all_goals nlinarith