import Mathlib

theorem algebra_167191 {p q : ℝ} (hp : 2*p^2-3*p-1=0) (hq : q^2+3*q-2=0) (hne : p*q≠1) :
    (23*p^4+125*q^4)/(17*p^4-q^4) = 2023 := by

  have hp2 : p^2 = (3 * p + 1) / 2 := by
    linarith
  
  have hq2 : q^2 = -3 * q + 2 := by
    linarith
  
  have hp4 : p^4 = (39 * p + 11) / 8 := by
    calc
      p^4 = (p^2) ^ 2 := by ring
      _ = ((3 * p + 1) / 2) ^ 2 := by rw [hp2]
      _ = (9 * p^2 + 6 * p + 1) / 4 := by ring_nf
      _ = (9 * ((3 * p + 1) / 2) + 6 * p + 1) / 4 := by rw [hp2]
      _ = (39 * p + 11) / 8 := by ring_nf
  
  have hq4 : q^4 = -39 * q + 22 := by
    calc
      q^4 = (q^2) ^ 2 := by ring
      _ = (-3 * q + 2) ^ 2 := by rw [hq2]
      _ = 9 * q^2 - 12 * q + 4 := by ring_nf
      _ = 9 * (-3 * q + 2) - 12 * q + 4 := by rw [hq2]
      _ = -39 * q + 22 := by ring_nf
  
  have eq1 : 23 * p^4 + 125 * q^4 = 2023 * (17 * p^4 - q^4) := by
    rw [hp4, hq4]
    nlinarith [sq_pos_of_ne_zero (show (p * q - 1) ≠ 0 by
      intro h'
      apply hne
      linarith
    ), sq_nonneg (p - q), sq_nonneg (p + q)]
  
  have hdenomne : 17 * p^4 - q^4 ≠ 0 := by
    by_contra h
    have eq2 : 23 * p^4 + 125 * q^4 = 0 := by
      nlinarith [eq1, h]
    have hp4_eq_zero : p^4 = 0 := by
      nlinarith [sq_nonneg p, sq_nonneg (p^2), sq_nonneg (p - 3 / 2), sq_nonneg (q + 3 / 2)]
    have hq4_eq_zero : q^4 = 0 := by
      nlinarith [sq_nonneg q, sq_nonneg (q^2), sq_nonneg (q + 3 / 2), sq_nonneg (p - 3 / 2)]
    have hp_eq_zero : p = 0 := by
      have h1 : p^4 = 0 := hp4_eq_zero
      nlinarith [sq_nonneg p, sq_nonneg (p^2)]
    have hq_eq_zero : q = 0 := by
      have h2 : q^4 = 0 := hq4_eq_zero
      nlinarith [sq_nonneg q, sq_nonneg (q^2)]
    have h16 : p * q = 1 := by
      have h17 : p * q = 0 := by
        rw [hp_eq_zero, hq_eq_zero]
        norm_num
      have h18 : p * q ≠ 1 := hne
      have h19 : p * q = 1 := by
        nlinarith [sq_pos_of_ne_zero (show (p * q - 1) ≠ 0 by
          intro h'
          apply hne
          linarith
        ), sq_nonneg (p - q), sq_nonneg (p * q - 1)]
      exact h19
    exfalso
    exact hne (by
      nlinarith [h16]
    )
  
  have h_eq : (23 * p^4 + 125 * q^4) = 2023 * (17 * p^4 - q^4) := by
    linarith [eq1]
  
  have : (23*p^4+125*q^4)/(17*p^4-q^4) = 2023 := by
    have h17p4ne : 17 * p^4 - q^4 ≠ 0 := hdenomne
    field_simp [h17p4ne]
    <;> nlinarith [h_eq, sq_pos_of_ne_zero (show (p * q - 1) ≠ 0 by
        intro h'
        apply hne
        linarith
      ), sq_nonneg (p - q), sq_nonneg (p * q - 1)]
  exact this