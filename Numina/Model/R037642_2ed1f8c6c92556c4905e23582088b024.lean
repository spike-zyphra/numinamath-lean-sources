import Mathlib

theorem algebra_104277 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 - b * c = b^2 - a * c) (h2 : b^2 - a * c = c^2 - a * b) :
    (a / (b + c) + 2 * b / (a + c) + 4 * c / (a + b)) = 7 / 2 ∨
    (a / (b + c) + 2 * b / (a + c) + 4 * c / (a + b)) = -7 := by
  by_cases h8 : a + b + c = 0 
  · -- Case where a + b + c = 0 
    have h5 : a + b = -c := by linarith
    have h6 : b + c = -a := by linarith
    have h7 : a + c = -b := by linarith
    have eq3 : a / (b + c) + 2 * b / (a + c) + 4 * c / (a + b) = -7 := by
      have h81 : b + c = -a := by linarith
      have h82 : a + c = -b := by linarith
      have h83 : a + b = -c := by linarith
      rw [show b + c = -a by linarith, show a + c = -b by linarith, show a + b = -c by linarith]
      field_simp [(show (-a) ≠ 0 by intro h; apply ha; linarith), 
                  (show (-b) ≠ 0 by intro h; apply hb; linarith), 
                  (show (-c) ≠ 0 by intro h; apply hc; linarith)]
      <;> ring_nf
    right
    linarith
  · -- Case where a + b + c ≠ 0 
    have h3 : (a - b) * (a + b + c) = 0 := by
      nlinarith
    have h4 : (b - c) * (a + b + c) = 0 := by
      nlinarith
    have ha1 : a - b = 0 := by
      apply (mul_left_inj' (show a + b + c ≠ 0 by assumption)).mp 
      linarith 
    have ha2 : b - c = 0 := by
      apply (mul_left_inj' (show a + b + c ≠ 0 by assumption)).mp 
      linarith 
    have ha11 : a = b := by linarith
    have ha12 : b = c := by linarith
    have ha13 : a = c := by linarith
    have eq3 : a / (b + c) + 2 * b / (a + c) + 4 * c / (a + b) = 7 / 2 := by 
      have h81 : b + c = 2 * a := by 
        nlinarith [ha11, ha12] 
      have h82 : a + c = 2 * a := by 
        nlinarith [ha11, ha12] 
      have h83 : a + b = 2 * a := by 
        nlinarith [ha11, ha12] 
      have eq3' : a / (b + c) + 2 * b / (a + c) + 4 * c / (a + b) = 7 / 2 := by
        rw [show b + c = 2 * a by linarith, show a + c = 2 * a by linarith, show a + b = 2 * a by linarith]
        have h91 : b = a := by linarith 
        have h92 : c = a := by linarith 
        rw [h91, h92] 
        field_simp [(show 2 * a ≠ 0 by 
            intro h11 
            apply ha 
            linarith 
          )] 
        ring
      linarith [eq3']
    left
    linarith [eq3]