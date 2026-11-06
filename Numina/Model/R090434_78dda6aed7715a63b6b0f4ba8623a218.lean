import Mathlib

theorem algebra_300728 {a : ℝ} (ha : 0 < a ∧ a < 1) :
    (Real.sqrt (a^2 + 1 / a^2 - 2)) / (1 + 1 / a) * (1 / (1 + a)) = (1 - a) / (1 + a) := by
  have ha1 : 0 < a := ha.1
  have ha2 : a < 1 := ha.2
  have h1 : a^2 + 1 / a^2 - 2 = (a - 1 / a) ^ 2 := by
    field_simp
    ring
  have h2 : Real.sqrt (a^2 + 1 / a^2 - 2) = (1 / a - a) := by
    rw [h1]
    have h3 : Real.sqrt ((a - 1 / a) ^ 2) = |a - 1 / a| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h3]
    have h4 : a - 1 / a < 0 := by
      have ha1' : 0 < a := ha1
      have ha2' : a < 1 := ha2
      have h6 : 1 / a > 1 := by
        have h7 : 0 < a := ha1
        have h8 : a < 1 := ha2
        apply (lt_div_iff₀' (by linarith)).mpr
        nlinarith
      linarith
    rw [abs_of_neg h4]
    ring_nf
    <;> field_simp <;> linarith
  rw [h2]
  have h5 : 1 + 1 / a = (a + 1) / a := by
    field_simp
    <;> ring
  rw [h5]
  have h5' : 1 + a > 0 := by
    nlinarith
  have ha' : a > 0 := by
    linarith
  field_simp
  <;> ring_nf <;> field_simp <;> nlinarith