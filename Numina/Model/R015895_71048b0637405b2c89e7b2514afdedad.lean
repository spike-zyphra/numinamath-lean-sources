import Mathlib

theorem algebra_205633 {a b p q : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hroots : p ≠ q) (hroots' : a ≠ b)
    (h1 : p^2 - a * p + b = 0) (h2 : q^2 - a * q + b = 0)
    (h3 : a^2 - p * a - q = 0) (h4 : b^2 - p * b - q = 0) :
    a = 1 ∧ b = -2 ∧ p = -1 ∧ q = 2 := by 
  have eq1 : (p - q) * (p + q - a) = 0 := by
    nlinarith
  have ha1 : p + q - a = 0 := by
    apply_fun (fun x => x / (p - q)) at eq1
    field_simp [(show p - q ≠ 0 by 
      intro h
      apply hroots
      linarith
    )] at eq1 
    <;> linarith

  have eq2 : (a - b) * (a + b - p) = 0 := by
    nlinarith

  have hp1 : a + b - p = 0 := by
    apply_fun (fun x => x / (a - b)) at eq2
    field_simp [(show a - b ≠ 0 by 
      intro h
      apply hroots'
      linarith
    )] at eq2 
    <;> nlinarith

  have eq3 : b * (a + b + 1) = 0 := by
    have eq4 : p = a + b := by linarith
    rw [eq4] at h1
    nlinarith

  have eq4 : a + b + 1 = 0 := by
    apply (mul_left_inj' hb).mp
    linarith

  have eq5 : p = a + b := by linarith

  have eq6 : q = -b := by
    have eq7 : p + q = a := by linarith [ha1]
    linarith [eq5, eq7]

  have eq7 : b * (-a + 1) = 0 := by
    rw [show p = a + b by linarith [eq5]] at h4
    rw [show q = -b by linarith [eq6]] at h4
    nlinarith

  have ha2 : a = 1 := by
    cases' (mul_eq_zero.1 eq7) with hb1 hb1
    · -- Case where b = 0, which contradicts hb 
      exfalso
      apply hb
      linarith 
    · -- Case where -a + 1 = 0, hence a = 1
      linarith

  have hb2 : b = -2 := by
    have eq6' : a + b + 1 = 0 := eq4
    rw [show a = 1 by linarith [ha2]] at eq6'
    linarith

  have hp2 : p = -1 := by
    nlinarith [ha2, hb2, eq5]

  have hq1 : q = 2 := by
    rw [hb2] at eq6 
    linarith

  exact ⟨ha2, hb2, hp2, hq1⟩