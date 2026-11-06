import Mathlib

open Real

theorem algebra_140683 {f g : ℝ → ℝ}
    (hf : f = fun x => sqrt (x ^ 2 - 4)) (hg : g = fun x => sqrt (x ^ 2 + 4))
    (a : ℝ) (ha : 0 < a ∧ a < 1) :
    f (a + 1 / a) + g (a - 1 / a) = 2 / a := by
  rcases ha with ⟨ha_pos, ha_lt_1⟩
  have h1 : f (a + 1 / a) = sqrt ((a + 1 / a) ^ 2 - 4) := by
    rw [hf]
  have h2 : g (a - 1 / a) = sqrt ((a - 1 / a) ^ 2 + 4) := by
    rw [hg]
  have h3 : (a + 1 / a) ^ 2 - 4 = (a - 1 / a) ^ 2 := by
    field_simp
    <;> ring
  have h4 : (a - 1 / a) ^ 2 + 4 = (a + 1 / a) ^ 2 := by
    field_simp
    <;> ring
  have h5 : f (a + 1 / a) = sqrt ((a - 1 / a) ^ 2) := by
    rw [h1]
    rw [h3]
  have h6 : g (a - 1 / a) = sqrt ((a + 1 / a) ^ 2) := by
    rw [h2]
    rw [h4]
  have h7 : sqrt ((a - 1 / a) ^ 2) = abs (a - 1 / a) := by
    rw [Real.sqrt_sq_eq_abs]
  have h8 : sqrt ((a + 1 / a) ^ 2) = abs (a + 1 / a) := by
    rw [Real.sqrt_sq_eq_abs]
  have h9 : a + 1 / a > 0 := by
    have ha_pos' : 0 < a := ha_pos
    have h1 : 1 / a > 0 := by
      apply div_pos
      linarith
      linarith
    linarith [show a > 0 by linarith, show 1 / a > 0 by linarith]
  have h11 : a - 1 / a < 0 := by
    have ha_pos' : 0 < a := ha_pos
    have ha_lt_1' : a < 1 := ha_lt_1
    have h1 : 1 / a > 1 := by
      have h2 : a * (1 / a) = 1 := by
        field_simp
      nlinarith
    nlinarith [show a > 0 by linarith, show 1 / a > 1 by linarith]
  have h12 : abs (a + 1 / a) = a + 1 / a := by
    rw [abs_of_pos]
    linarith
  have h13 : abs (a - 1 / a) = -(a - 1 / a) := by
    rw [abs_of_neg]
    linarith
    all_goals linarith
  rw [h5, h6, h7, h8, h12, h13]
  field_simp
  <;> ring_nf <;> field_simp <;> ring