import Mathlib

theorem number_theory_13806 {P Q R : ℕ} (hP : P ≠ Q) (hQR : Q ≠ R) (hPR : P ≠ R)
    (h1 : Nat.digits 8 n = [R, Q, P, 1]) (h2 : Nat.digits 11 n = [Q, P, R]) :
    n = 766 := by
  have h3 : n = 512 + 64 * P + 8 * Q + R := by
    rw [← Nat.ofDigits_digits 8 n]
    rw [h1]
    simp [Nat.ofDigits]
    all_goals omega
  have h4 : n = 121 * R + 11 * P + Q := by
    rw [← Nat.ofDigits_digits 11 n]
    rw [h2]
    simp [Nat.ofDigits]
    all_goals omega
  have h5 : 53 * P + 7 * Q = 120 * R - 512 := by
    omega
  have hPR' : P < 8 := by
    have h1' : ∀ d ∈ Nat.digits 8 n, d < 8 := by
      intros d hd
      apply Nat.digits_lt_base (by norm_num) hd
    have hP : P ∈ Nat.digits 8 n := by
      rw [h1]
      simp
    specialize h1' P hP
    linarith
  have hQR' : Q < 8 := by
    have h1' : ∀ d ∈ Nat.digits 8 n, d < 8 := by
      intros d hd
      apply Nat.digits_lt_base (by norm_num) hd
    have hQ : Q ∈ Nat.digits 8 n := by
      rw [h1]
      simp
    specialize h1' Q hQ
    linarith
  have hRR' : R < 8 := by
    have h1' : ∀ d ∈ Nat.digits 8 n, d < 8 := by
      intros d hd
      apply Nat.digits_lt_base (by norm_num) hd
    have hR : R ∈ Nat.digits 8 n := by
      rw [h1]
      simp
    specialize h1' R hR
    linarith
  have hP3 : P = 3 := by
    interval_cases P <;> interval_cases Q <;> interval_cases R <;> omega
  have hQ7 : Q = 7 := by
    interval_cases P <;> interval_cases Q <;> interval_cases R <;> omega
  have hR6 : R = 6 := by
    interval_cases P <;> interval_cases Q <;> interval_cases R <;> omega
  rw [hP3, hQ7, hR6] at h3
  omega