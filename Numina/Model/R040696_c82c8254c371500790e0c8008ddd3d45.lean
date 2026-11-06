import Mathlib

  theorem algebra_90330 : {(a, b) : ℝ × ℝ | 2*(a^2+1)*(b^2+1) = (a+1)*(b+1)*(a*b+1)} = {(1, 1)} := by
  ext ⟨a, b⟩
  simp
  constructor
  · -- First, assume that \( 2(a^2+1)(b^2+1) = (a+1)(b+1)(ab+1) \), therefore \( (a, b) = (1, 1) \).
    intro h
    have eq1 : (a - 1) ^ 2 * (b - 1) ^ 2 = (a - 1) * (b - 1) := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a * (b - 1)), sq_nonneg ((b) * (a - 1)), sq_nonneg (a + b - 2)]
    have eq2 : (a - 1) * (b - 1) * ((a - 1) * (b - 1) - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq2) with eq3 eq4
    · -- If (a - 1) * (b - 1) = 0, then either a = 1 or b = 1.
      have eq5 : (a - 1) = 0 ∨ (b - 1) = 0 := by
        cases (mul_eq_zero.mp eq3) with
        | inl h => 
          left
          linarith
        | inr h => 
          right
          linarith
      cases eq5 with
      | inl ha => 
        have ha' : a = 1 := by linarith
        rw [ha'] at h 
        have hb : b = 1 := by nlinarith 
        simp [ha', hb]
      | inr hb => 
        have hb' : b = 1 := by linarith 
        rw [hb'] at h 
        have ha : a = 1 := by nlinarith 
        simp [ha, hb']
    · -- If (a - 1) * (b - 1) - 1 = 0, then (a - 1) * (b - 1) = 1.
      have eq5 : (a - 1) * (b - 1) = 1 := by linarith 
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a * (b - 1)), sq_nonneg ((b) * (a - 1)), sq_nonneg (a + b - 2)]
  · -- Now, show that (1, 1) is in the set.
    rintro ⟨rfl, rfl⟩
    norm_num