import Mathlib

theorem algebra_9672 {a b : ℝ} (ha : a ≠ b) (h : a^2 = 20*a-23 ∧ b^2 = 20*b-23) : a/b + b/a = 15+9/23 := by
  rcases h with ⟨ha2, hb2⟩

  have hbne : b ≠ 0 := by
    by_contra h'
    rw [h'] at hb2
    nlinarith
  
  have ha2ne : a ≠ 0 := by
    by_contra h'
    rw [h'] at ha2
    nlinarith

  have hsum : a + b = 20 := by
    have h_diff : a^2 - b^2 = 20 * (a - b) := by
      nlinarith

    have hyne : a - b ≠ 0 := by 
      intro h'
      apply ha
      linarith

    have h_eq : (a - b) * (a + b - 20) = 0 := by
      nlinarith

    cases' (mul_eq_zero.mp h_eq) with h3 h4
    · exfalso
      apply hyne
      linarith
    · linarith

  have hab : a * b = 23 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h'
      apply ha
      nlinarith), sq_pos_of_ne_zero (show b ≠ 0 by
        by_contra hb0
        rw [hb0] at hb2 
        nlinarith
      ), sq_pos_of_ne_zero (show a ≠ 0 by
        by_contra ha0
        rw [ha0] at ha2 
        nlinarith
      ) ]

  have h1 : a / b + b / a = (a^2 + b^2) / (a * b) := by
    field_simp [hbne, ha2ne]
    <;> ring

  have ha2b2 : a^2 + b^2 = 354 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h'
      apply ha
      nlinarith), sq_pos_of_ne_zero (show b ≠ 0 by
        by_contra hb0
        rw [hb0] at hb2 
        nlinarith
      ), sq_pos_of_ne_zero (show a ≠ 0 by
        by_contra ha0
        rw [ha0] at ha2 
        nlinarith
      ) ]

  rw [h1]
  rw [ha2b2, hab]
  all_goals norm_num