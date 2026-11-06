import Mathlib

theorem algebra_608014 {a b c : ℝ} (h₀ : a^2 + b^2 = 2 * c^2) (h₁ : a ≠ b)
    (h₂ : c ≠ -a) (h₃ : c ≠ -b) :
    ∃ k : ℤ, ((a + b + 2 * c) * (2 * a^2 - b^2 - c^2)) / ((a - b) * (a + c) * (b + c)) = k := by

  have ha1 : a - b ≠ 0 := by
    intro h
    apply h₁
    linarith

  have ha2 : a + c ≠ 0 := by
    intro h
    have h4 : c = -a := by linarith
    tauto

  have ha3 : b + c ≠ 0 := by
    intro h
    have h4 : c = -b := by linarith
    tauto

  use 3

  have eq1 : (a + b + 2 * c) * (2 * a^2 - b^2 - c^2) = 3 * ((a - b) * (a + c) * (b + c)) := by
    have eq4 : (a + b + 2 * c) * (a + b) = 2 * ((a + c) * (b + c)) := by
      nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
        intro h
        apply h₁
        linarith
      ), sq_pos_of_ne_zero (show (a + c) ≠ 0 by
        intro h
        apply h₂
        linarith
      ), sq_pos_of_ne_zero (show (b + c) ≠ 0 by
        intro h
        apply h₃
        linarith
      )]

    calc
      (a + b + 2 * c) * (2 * a^2 - b^2 - c^2) = (a + b + 2 * c) * ((3 / 2) * (a^2 - b^2)) := by
        have eq2 : 2 * a^2 - b^2 - c^2 = (3 / 2) * (a^2 - b^2) := by
          have h7 : c^2 = (a^2 + b^2) / 2 := by linarith
          rw [h7]
          nlinarith
        rw [eq2]
      _ = (a + b + 2 * c) * ((3 / 2) * ((a - b) * (a + b))) := by
        have eq3 : a^2 - b^2 = (a - b) * (a + b) := by ring
        rw [eq3]
      _ = (3 / 2) * ((a + b + 2 * c) * ((a - b) * (a + b))) := by ring
      _ = (3 / 2) * ((a - b) * ((a + b + 2 * c) * (a + b))) := by ring
      _ = (3 / 2) * ((a - b) * (2 * ((a + c) * (b + c)))) := by
        rw [eq4]
      _ = 3 * ((a - b) * ((a + c) * (b + c))) := by ring
      _ = 3 * ((a - b) * (a + c) * (b + c)) := by ring

  have h7 : ((a + b + 2 * c) * (2 * a^2 - b^2 - c^2)) / ((a - b) * (a + c) * (b + c)) = (3 : ℝ) := by
    rw [eq1]
    field_simp [ha1, ha2, ha3]
    all_goals ring

  norm_num at h7 ⊢
  all_goals linarith