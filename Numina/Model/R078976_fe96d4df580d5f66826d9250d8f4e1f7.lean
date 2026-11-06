import Mathlib

theorem algebra_225721 (a : ℤ) :
    (∃ x y, x ≠ y ∧ x^2 + a * x + 2 * a = 0 ∧ y^2 + a * y + 2 * a = 0) ↔
    a = -1 ∨ a = 9 := by 
  constructor
  · -- (→) Assume there exist two distinct integer roots, prove a = -1 or 9
    rintro ⟨x, y, hneq, hx, hy⟩
    have h_eq1 : x^2 + a * x + 2 * a - (y^2 + a * y + 2 * a) = 0 := by
      linarith 
    have eq2 : (x - y) * (x + y + a) = 0 := by
      nlinarith [h_eq1]
    cases' (mul_eq_zero.mp eq2) with hxy hxy'
    · -- Case: x - y = 0, contradiction with x ≠ y
      exfalso 
      exact hneq (by linarith)
    · -- Case: x + y + a = 0
      have ha : a = -(x + y) := by linarith
      rw [ha] at hx
      have eq2 : x * y + 2 * x + 2 * y = 0 := by 
        nlinarith 
      have eq3 : (x + 2) * (y + 2) = 4 := by 
        nlinarith [eq2] 
      have h1 : (x + 2) ∣ 4 := by 
        use (y + 2)
        linarith 
      have h2 : (x + 2) ≥ -4 := by 
        have h3 : (x + 2) ∣ 4 := h1 
        have h4 : (x + 2) ≤ 4 := by 
          apply Int.le_of_dvd (by norm_num) h3 
        have h5 : (x + 2) ≥ -4 := by 
          have h6 : (- (x + 2)) ∣ 4 := by 
            exact Int.neg_dvd.2 h3 
          have h7 : (- (x + 2)) ≤ 4 := by 
            apply Int.le_of_dvd (by norm_num) h6 
          linarith 
        linarith 
      have h3 : (x + 2) ≤ 4 := by 
        have h4 : (x + 2) ∣ 4 := h1 
        have h5 : (x + 2) ≤ 4 := by 
          apply Int.le_of_dvd (by norm_num) h4 
        linarith 
      interval_cases h4 : (x + 2) <;> try { 
        omega 
        <;> try { 
          have eq3' : (y + 2) = 4 := by 
            nlinarith [eq3] 
          <;> omega 
        }
      }
      <;> omega 
  · -- (←) Assume a = -1 or a = 9, prove there exist two distinct integer roots
    rintro (h | h)
    · -- Case a = -1 
      rw [h]
      use 2, -1
      constructor
      · -- Show x ≠ y
        norm_num 
      constructor
      · -- Show 2 is a root 
        norm_num 
      · -- Show -1 is a root 
        norm_num 
    · -- Case a = 9 
      rw [h]
      use -3, -6
      constructor
      · -- Show x ≠ y 
        norm_num 
      constructor
      · -- Show -3 is a root 
        norm_num 
      · -- Show -6 is a root 
        norm_num