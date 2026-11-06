import Mathlib

theorem algebra_20131 {p q : ℝ} (hp : p^2-2*p-3=0) (hq : q^2-2*q-3=0) (hne : p≠q) :
    (p+1)*(q+1)=0 := by
  have hp_eq : (p - 3) * (p + 1) = 0 := by
    linarith
  have hq_eq : (q - 3) * (q + 1) = 0 := by
    linarith
  have hp_eq_1 : p = 3 ∨ p = -1 := by
    cases (mul_eq_zero.mp hp_eq) with
    | inl h1 => 
      left
      linarith
    | inr h2 =>
      right
      linarith
  have hq_eq_1 : q = 3 ∨ q = -1 := by
    cases (mul_eq_zero.mp hq_eq) with
    | inl h1 => 
      left
      linarith
    | inr h2 =>
      right
      linarith
  cases hp_eq_1 with
  | inl hp3 =>
    cases hq_eq_1 with
    | inl hq3 =>
      exfalso
      exact hne (by linarith)
    | inr hq1 =>
      rw [hp3, hq1]
      norm_num
  | inr hp1 =>
    cases hq_eq_1 with
    | inl hq3 =>
      rw [hp1, hq3]
      norm_num
    | inr hq1 =>
      exfalso
      exact hne (by linarith)