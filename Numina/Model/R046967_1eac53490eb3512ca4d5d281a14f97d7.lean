import Mathlib
theorem algebra_608304 : {(a, b) : ℝ × ℝ | a - 10 = b - a ∧ b - a = a * b - b} = {(4, -2), (5 / 2, -5)}:= by
  ext ⟨a, b⟩
  simp
  constructor
  · -- First direction: the pair (a,b) satisfies both conditions => (4, -2) or (5/2, -5)
    rintro ⟨h₁, h₂⟩
    have eq1 : 2 * a - b = 10 := by
      linarith
    have eq2 : a * b + a - 2 * b = 0 := by
      nlinarith
    have eq3 : b = 2 * a - 10 := by
      linarith
    rw [eq3] at eq2
    have h3 : 2 * a^2 - 13 * a + 20 = 0 := by 
      nlinarith
    have h4 : (a - 4) * (a - 5 / 2) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h4) with ha1 ha2
    · -- First case: a = 4.
      have ha : a = 4 := by linarith
      have hb : b = -2 := by 
        rw [ha] at eq3
        linarith
      left
      simp [ha, hb]
    · -- Second case: a = 5/2.
      have ha : a = 5 / 2 := by linarith
      have hb : b = -5 := by 
        rw [ha] at eq3
        nlinarith
      right
      simp [ha, hb]
  · -- Backward implication: the pairs (4, -2) and (5/2, -5) satisfy both conditions.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- First pair: (4, -2).
      constructor
      · -- First condition: a - 10 = b - a.
        norm_num
      · -- Second condition: b - a = a * b - b.
        norm_num
    · -- Second pair: (5/2, -5).
      constructor
      · -- First condition: a - 10 = b - a.
        norm_num
      · -- Second condition: b - a = a * b - b.
        norm_num