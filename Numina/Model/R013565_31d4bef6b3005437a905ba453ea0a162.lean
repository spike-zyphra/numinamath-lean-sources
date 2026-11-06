import Mathlib

theorem algebra_165636 (a b c u v w : ℤ) (h₀ : u ≠ v) (h₁ : u ≠ w) (h₂ : v ≠ w)
    (h₃ : a * u ^ 2 + b * u + c = 0) (h₄ : a * v ^ 2 + b * v + c = 0)
    (h₅ : a * w ^ 2 + b * w + c = 2) :
    b ^ 2 - 4 * a * c ≤ 16 := by
  have eq1 : a * (u + v) + b = 0 := by
    have h6 : u - v ≠ 0 := by
      intro h
      apply h₀
      omega
    have eq : a * (u ^ 2 - v ^ 2) + b * (u - v) = 0 := by
      nlinarith
    have eq2 : a * (u - v) * (u + v) + b * (u - v) = 0 := by
      ring_nf at eq ⊢
      omega
    have eq3 : a * (u + v) + b = 0 := by
      apply (mul_left_inj' h6).mp
      linarith
    linarith
  have h8 : (w - u) ∣ 2 := by
    use (a * (w + u) + b)
    nlinarith
  have h9 : (w - u) = 1 ∨ (w - u) = 2 ∨ (w - u) = -1 ∨ (w - u) = -2 := by
    have h8 : (w - u) ∣ 2 := by
      use (a * (w + u) + b)
      nlinarith
    have h10 : (w - u) ≤ 2 := by
      exact Int.le_of_dvd (by norm_num) h8
    have h11 : (w - u) ≥ -2 := by
      have h12 : (- (w - u)) ∣ 2 := by
        exact Int.neg_dvd.2 h8
      have h13 : (- (w - u)) ≤ 2 := by
        exact Int.le_of_dvd (by norm_num) h12
      omega
    interval_cases (w - u) <;> omega
  rcases h9 with h9 | h9 | h9 | h9
  · -- Case w - u = 1
    have eq3 : (a * (w + u) + b) = 2 := by
      have h14 : (w - u) = 1 := h9
      have h15 : (a * (w + u) + b) * (w - u) = 2 := by
        nlinarith
      rw [show (w - u : ℤ) = 1 by linarith] at h15
      omega
    have eq4 : a * (w - v) = 2 := by
      nlinarith [eq1, eq3]
    have h10 : (u - v) ≠ 0 := by
      intro h
      apply h₀
      omega
    have eq5 : b = -a * (u + v) := by linarith
    have eq6 : c = a * u * v := by
      rw [eq5] at h₃
      nlinarith
    have h11 : a * (w - v) = 2 := by
      nlinarith [eq1, eq3]
    have eq7 : w - v = 1 + (u - v) := by
      have h9' : w - u = 1 := h9
      have eq8 : w - u = 1 := h9
      omega
    have h12 : a ∣ 2 := by 
      have eq8 : a * (w - v) = 2 := by 
        linarith 
      have eq9 : a ∣ 2 := by 
        use w - v 
        linarith 
      tauto 
    have h13 : a = 1 ∨ a = 2 ∨ a = -1 ∨ a = -2 := by 
      have h14 : a ∣ 2 := h12 
      have h15 : a ≤ 2 := by 
        exact Int.le_of_dvd (by norm_num) h14 
      have h16 : a ≥ -2 := by 
        have h17 : (-a) ∣ 2 := by 
          exact Int.neg_dvd.2 h14 
        have h18 : -a ≤ 2 := by 
          exact Int.le_of_dvd (by norm_num) h17
        omega 
      interval_cases a <;> try tauto 
    rcases h13 with h14 | h14 | h14 | h14
    · -- a = 1
      have ha1 : a = 1 := h14 
      have h14' : w - v = 2 := by 
        rw [ha1] at h11 
        omega 
      have h15 : u - v = 1 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha1]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
    · -- a = 2
      have ha2 : a = 2 := h14 
      have h14' : w - v = 1 := by 
        rw [ha2] at h11 
        omega 
      have h15 : u - v = 0 := by 
        omega 
      omega 
    · -- a = -1
      have ha3 : a = -1 := h14 
      have h14' : w - v = -2 := by 
        rw [ha3] at h11 
        omega 
      have h15 : u - v = -3 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha3]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
    · -- a = -2
      have ha4 : a = -2 := h14 
      have h14' : w - v = -1 := by 
        rw [ha4] at h11 
        omega 
      have h15 : u - v = -2 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha4]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
  · -- Case w - u = 2
    have eq3 : (a * (w + u) + b) = 1 := by
      have h14 : (w - u) = 2 := h9
      have h15 : (a * (w + u) + b) * (w - u) = 2 := by
        nlinarith
      rw [show (w - u : ℤ) = 2 by linarith] at h15
      omega
    have eq4 : a * (w - v) = 1 := by
      nlinarith [eq1, eq3]
    have h10 : (u - v) ≠ 0 := by 
      intro h 
      apply h₀ 
      omega 
    have eq5 : b = -a * (u + v) := by linarith 
    have eq6 : c = a * u * v := by
      rw [eq5] at h₃
      nlinarith
    have h11 : a * (w - v) = 1 := by
      nlinarith [eq1, eq3]
    have eq7 : w - v = 2 + (u - v) := by
      have h9' : w - u = 2 := h9 
      have eq8 : w - u = 2 := h9
      omega 
    have h12 : a = 1 ∨ a = -1 := by
      have h13 : a ∣ 1 := by
        have h14 : a * (w - v) = 1 := h11
        have eq9 : a ∣ 1 := by 
          use w - v 
          all_goals linarith 
        tauto
      have h14 : a = 1 ∨ a = -1 := by 
        have h15 : a ∣ 1 := h13 
        have h16 : a ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h15 
        have h17 : a ≥ -1 := by 
          have h18 : (-a) ∣ 1 := by 
            exact Int.neg_dvd.2 h15 
          have h19 : -a ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h18 
          omega 
        interval_cases a <;> tauto 
      assumption 
    rcases h12 with h13 | h13 
    · -- a = 1
      have ha1 : a = 1 := h13 
      have h14' : w - v = 1 := by 
        rw [ha1] at h11 
        omega 
      have h15 : u - v = -1 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha1]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
    · -- a = -1
      have ha2 : a = -1 := h13 
      have h14' : w - v = -1 := by 
        rw [ha2] at h11 
        omega 
      have h15 : u - v = -3 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha2]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
  · -- Case w - u = -1
    have eq3 : (a * (w + u) + b) = -2 := by
      have h14 : (w - u) = -1 := h9
      have h15 : (a * (w + u) + b) * (w - u) = 2 := by
        nlinarith
      rw [show (w - u : ℤ) = -1 by linarith] at h15
      omega
    have eq4 : a * (w - v) = -2 := by
      nlinarith [eq1, eq3]
    have h10 : (u - v) ≠ 0 := by 
      intro h 
      apply h₀ 
      omega 
    have eq5 : b = -a * (u + v) := by linarith 
    have eq6 : c = a * u * v := by
      rw [eq5] at h₃
      nlinarith
    have h11 : a * (w - v) = -2 := by
      nlinarith [eq1, eq3]
    have eq7 : w - v = -1 + (u - v) := by
      have h9' : w - u = -1 := h9 
      have eq8 : w - u = -1 := h9
      omega 
    have h12 : a ∣ 2 := by 
      have h13 : a * (w - v) = -2 := h11 
      have eq9 : a ∣ 2 := by 
        use -(w - v)
        all_goals linarith 
      tauto 
    have h13 : a = 1 ∨ a = 2 ∨ a = -1 ∨ a = -2 := by
      have h14 : a ∣ 2 := h12 
      have h15 : a ≤ 2 := by 
        exact Int.le_of_dvd (by norm_num) h14 
      have h16 : a ≥ -2 := by 
        have h17 : (-a) ∣ 2 := by 
          exact Int.neg_dvd.2 h14 
        have h18 : -a ≤ 2 := by 
          exact Int.le_of_dvd (by norm_num) h17 
        omega 
      interval_cases a <;> tauto 
    rcases h13 with h14 | h14 | h14 | h14
    · -- a = 1
      have ha1 : a = 1 := h14 
      have h14' : w - v = -2 := by 
        rw [ha1] at h11 
        omega 
      have h15 : u - v = -1 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha1]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
    · -- a = 2
      have ha2 : a = 2 := h14 
      have h14' : w - v = -1 := by 
        rw [ha2] at h11 
        omega 
      have h15 : u - v = 0 := by 
        omega 
      omega 
    · -- a = -1
      have ha3 : a = -1 := h14 
      have h14' : w - v = 2 := by 
        rw [ha3] at h11 
        omega 
      have h15 : u - v = 3 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha3]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
    · -- a = -2
      have ha4 : a = -2 := h14 
      have h14' : w - v = 1 := by 
        rw [ha4] at h11 
        omega 
      have h15 : u - v = 2 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha4]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
  · -- Case w - u = -2
    have eq3 : (a * (w + u) + b) = -1 := by 
      have h14 : (w - u) = -2 := h9 
      have h15 : (a * (w + u) + b) * (w - u) = 2 := by 
        nlinarith 
      rw [show (w - u : ℤ) = -2 by linarith] at h15 
      omega 
    have eq4 : a * (w - v) = -1 := by 
      nlinarith [eq1, eq3] 
    have h10 : (u - v) ≠ 0 := by
      intro h
      apply h₀
      omega 
    have eq5 : b = -a * (u + v) := by linarith 
    have eq6 : c = a * u * v := by 
      rw [eq5] at h₃ 
      nlinarith 
    have h11 : a * (w - v) = -1 := by 
      nlinarith [eq1, eq3] 
    have eq7 : w - v = -2 + (u - v) := by
      have h9' : w - u = -2 := h9 
      have eq8 : w - u = -2 := h9
      omega 
    have h12 : a = 1 ∨ a = -1 := by 
      have h13 : a ∣ 1 := by 
        have h14 : a * (w - v) = -1 := h11 
        have eq9 : a ∣ 1 := by 
          use -(w - v)
          all_goals linarith 
        tauto 
      have h14 : a = 1 ∨ a = -1 := by
        have h15 : a ∣ 1 := h13 
        have h16 : a ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h15 
        have h17 : a ≥ -1 := by 
          have h18 : (-a) ∣ 1 := by 
            exact Int.neg_dvd.2 h15 
          have h19 : -a ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h18 
          omega 
        interval_cases a <;> tauto 
      assumption 
    rcases h12 with h13 | h13 
    · -- a = 1 
      have ha1 : a = 1 := h13 
      have h14' : w - v = -1 := by 
        rw [ha1] at h11 
        omega 
      have h15 : u - v = 1 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha1]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]
    · -- a = -1 
      have ha2 : a = -1 := h13 
      have h14' : w - v = 1 := by 
        rw [ha2] at h11 
        omega 
      have h15 : u - v = 3 := by 
        omega 
      have eq5' : b = -a * (u + v) := eq5 
      have eq6' : c = a * u * v := eq6 
      rw [eq5', eq6', ha2]
      nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), h10]