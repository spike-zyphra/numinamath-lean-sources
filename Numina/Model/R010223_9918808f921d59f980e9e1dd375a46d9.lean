import Mathlib

theorem algebra_20131 {p q : ℝ} (hp : p^2-2*p-3=0) (hq : q^2-2*q-3=0) (hne : p≠q) :
    (p+1)*(q+1)=0 := by
  have h1 : (p - 3) * (p + 1) = 0 := by
    linarith
  have h2 : (q - 3) * (q + 1) = 0 := by
    linarith

  cases (mul_eq_zero.mp h1) with
  | inl hp3 =>
    have hp_eq_3 : p = 3 := by linarith
    have hq_eq : q = -1 := by
      cases (mul_eq_zero.mp h2) with
      | inl hq3 =>
        have hq_eq_3 : q = 3 := by linarith
        exfalso
        exact hne (by linarith)
      | inr hq1 =>
        linarith
    rw [hp_eq_3, hq_eq]
    norm_num
  | inr hp1 =>
    have hp_eq_neg1 : p = -1 := by linarith
    have hq_eq : q = 3 := by
      cases (mul_eq_zero.mp h2) with
      | inl hq3 =>
        linarith
      | inr hq1 =>
        have hq_eq_neg1 : q = -1 := by linarith
        exfalso
        exact hne (by linarith)
    rw [hp_eq_neg1, hq_eq]
    norm_num