import Mathlib

theorem algebra_102206 {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a / (b + c) = b / (a + c)) (h2 : b / (a + c) = c / (a + b)) :
    ∃ q : ℚ, Real.sqrt ((a + b) / (a + 2 * b + 3 * c) + (b + c) / (b + 2 * c + 3 * a) +
      (c + a) / (c + 2 * a + 3 * b)) = q ∧
    ¬∃ q : ℚ, Real.sqrt ((a * b) / (c * (2 * a - b)) + (b * c) / (a * (2 * b - c)) +
      (c * a) / (b * (2 * c - a))) = q := by

  have h3 : a * (a + c) = b * (b + c) := by
    have h3 : b + c ≠ 0 := by positivity
    have h4 : a + c ≠ 0 := by positivity
    field_simp [h3, h4] at h1 ⊢
    linarith
  have h4 : b * (a + b) = c * (a + c) := by
    have h5 : a + c ≠ 0 := by positivity
    have h6 : a + b ≠ 0 := by positivity
    field_simp [h5, h6] at h2 ⊢
    linarith
  have h5 : a = b := by
    have eq1 : a * (a + c) = b * (b + c) := h3
    have eq3 : (a - b) * (a + b + c) = 0 := by
      linarith [eq1]
    have h6 : a + b + c > (0 : ℚ) := by
      linarith [ha, hb, hc]
    have h7 : a - b = 0 := by
      apply (mul_right_inj' (show (a + b + c : ℚ) ≠ 0 by positivity)).mp
      linarith
    linarith
  have h11 : a = c := by
    have eq1 : a * (a + c) = b * (b + c) := h3
    have eq2 : b * (a + b) = c * (a + c) := h4
    have eq4 : (b - c) * (a + b + c) = 0 := by
      nlinarith [eq2]
    have h6 : a + b + c > (0 : ℚ) := by
      linarith [ha, hb, hc]
    have h8 : b = a := by
      linarith [h5]
    rw [h8] at eq4
    have eq5 : (a - c) * (2 * a + c) = 0 := by
      nlinarith [eq4]
    have h10 : 2 * a + c > 0 := by
      nlinarith [ha, hc]
    have h9 : a - c = 0 := by
      apply (mul_right_inj' (show (2 * a + c : ℚ) ≠ 0 by positivity)).mp
      linarith
    linarith

  use (1 : ℚ)
  constructor
  · -- Show that $\sqrt{\frac{a+b}{a+2b+3c}+\frac{b+c}{b+2c+3a}+\frac{c+a}{c+2a+3b}} = 1$
    have h12 : (a + b) / (a + 2 * b + 3 * c) + (b + c) / (b + 2 * c + 3 * a) + (c + a) / (c + 2 * a + 3 * b) = (1 : ℝ) := by
      have ha1 : (a : ℝ) > (0 : ℝ) := by exact_mod_cast ha
      have hb1 : (b : ℝ) > (0 : ℝ) := by exact_mod_cast hb
      have hc1 : (c : ℝ) > (0 : ℝ) := by exact_mod_cast hc
      have h13 : (a : ℝ) = (b : ℝ) := by exact_mod_cast h5
      have h14 : (a : ℝ) = (c : ℝ) := by exact_mod_cast h11
      rw [show (b : ℝ) = (a : ℝ) by linarith [h13], show (c : ℝ) = (a : ℝ) by linarith [h14]]
      field_simp [(show (a : ℝ) ≠ 0 by positivity)]
      <;> nlinarith
    have h15 : Real.sqrt ((a + b) / (a + 2 * b + 3 * c) + (b + c) / (b + 2 * c + 3 * a) +
      (c + a) / (c + 2 * a + 3 * b)) = (1 : ℝ) := by
      rw [h12]
      all_goals norm_num
    exact_mod_cast h15
  · -- Show that $\sqrt{\frac{ab}{c(2a-b)}+\frac{bc}{a(2b-c)}+\frac{ca}{b(2c-a)}} \in \mathbb{R} \setminus \mathbb{Q}$
    intro h
    rcases h with ⟨q, hq⟩
    have h14 : (a * b : ℝ) / (c * (2 * a - b)) + (b * c : ℝ) / (a * (2 * b - c)) + (c * a : ℝ) / (b * (2 * c - a)) = (3 : ℝ) := by
      have h13 : (a : ℝ) = (b : ℝ) := by exact_mod_cast h5
      have h14 : (a : ℝ) = (c : ℝ) := by exact_mod_cast h11
      have h15 : (b : ℝ) = (a : ℝ) := by linarith [h13]
      have h16 : (c : ℝ) = (a : ℝ) := by linarith [h14]
      have eq1 : (a * b : ℝ) = (a * a : ℝ) := by
        rw [show (b : ℝ) = (a : ℝ) by linarith [h15]]
      have eq2 : (b * c : ℝ) = (a * a : ℝ) := by
        rw [show (b : ℝ) = (a : ℝ) by linarith [h15], show (c : ℝ) = (a : ℝ) by linarith [h16]]
      have eq3 : (c * a : ℝ) = (a * a : ℝ) := by
        rw [show (c : ℝ) = (a : ℝ) by linarith [h16]]
      have eq4 : (c * (2 * a - b) : ℝ) = (a * a : ℝ) := by
        rw [show (b : ℝ) = (a : ℝ) by linarith [h15], show (c : ℝ) = (a : ℝ) by linarith [h16]]
        ring_nf
      have eq5 : (a * (2 * b - c) : ℝ) = (a * a : ℝ) := by
        rw [show (b : ℝ) = (a : ℝ) by linarith [h15], show (c : ℝ) = (a : ℝ) by linarith [h16]]
        ring_nf
      have eq6 : (b * (2 * c - a) : ℝ) = (a * a : ℝ) := by
        rw [show (b : ℝ) = (a : ℝ) by linarith [h15], show (c : ℝ) = (a : ℝ) by linarith [h16]]
        ring_nf
      rw [eq1, eq2, eq3, eq4, eq5, eq6]
      have ha2 : (a : ℝ) ≠ 0 := by positivity
      field_simp [ha2]
      <;> ring
    have h17 : Real.sqrt ((a * b) / (c * (2 * a - b)) + (b * c) / (a * (2 * b - c)) +
      (c * a) / (b * (2 * c - a))) = Real.sqrt (3 : ℝ) := by
      rw [h14]
    rw [h17] at hq
    have h18 : Real.sqrt (3 : ℝ) = (q : ℝ) := by
      linarith [hq]
    have h19 : Irrational (Real.sqrt (3 : ℝ)) := by
      native_decide
    have h20 : ¬ Irrational (Real.sqrt (3 : ℝ)) := by
      rw [h18]
      simp
    contradiction