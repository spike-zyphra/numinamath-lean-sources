import Mathlib

theorem inequalities_140447 (a b p q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 1 < p) (hq : 1 < q) (h : 1 / p + 1 / q = 1) :
    a ^ ((1 : ℝ) / p) * b ^ ((1 : ℝ) / q) ≤ a / p + b / q := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hq_pos : (0 : ℝ) < q := by linarith
  have hw1 : (1 / p : ℝ) ≥ 0 := by
    have hp_pos : (0 : ℝ) < p := by linarith
    positivity
  have hw2 : (1 / q : ℝ) ≥ 0 := by
    have hq_pos : (0 : ℝ) < q := by linarith
    positivity
  have hw : (1 / p : ℝ) + (1 / q : ℝ) = 1 := h
  have h11 : a ^ ((1 : ℝ) / p) * b ^ ((1 : ℝ) / q) ≤ (a / p + b / q) := by
    have h13 : a ^ ((1 : ℝ) / p) * b ^ ((1 : ℝ) / q) ≤ (1 / p : ℝ) * a + (1 / q : ℝ) * b := by
      have h2 : (1 / p : ℝ) ≥ 0 := hw1
      have h3 : (1 / q : ℝ) ≥ 0 := hw2
      have h4 : (1 / p : ℝ) + (1 / q : ℝ) = 1 := hw
      have h14 : a ^ ((1 : ℝ) / p) * b ^ ((1 : ℝ) / q) = (Real.rpow a (1 / p)) * (Real.rpow b (1 / q)) := by
        simp [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
        <;> ring_nf
        all_goals
          try { tauto }
          try { linarith }
          try { ring }
      rw [h14]
      have h15 : (Real.rpow a (1 / p)) * (Real.rpow b (1 / q)) ≤ (1 / p : ℝ) * a + (1 / q : ℝ) * b := by
        apply Real.geom_mean_le_arith_mean2_weighted
        all_goals
          try { linarith }
          try { positivity }
          try { tauto }
      linarith
    have h18 : (1 / p : ℝ) * a + (1 / q : ℝ) * b = a / p + b / q := by
      field_simp
      <;> ring_nf <;> field_simp
      <;> ring_nf <;> linarith
    linarith
  linarith