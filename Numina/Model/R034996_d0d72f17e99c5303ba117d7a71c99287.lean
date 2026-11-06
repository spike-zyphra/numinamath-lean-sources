import Mathlib

theorem algebra_166710 {p q : ℝ} (hroots : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ |x - y| = 5 ∧ |x^3 - y^3| = 35) :
    p = 1 ∧ q = -6 ∨ p = -1 ∧ q = -6 := by 
  rcases hroots with ⟨x, y, hxy, hx, hy, h1, h2⟩
  have eq1 : (x - y) * (x + y + p) = 0 := by
    nlinarith
  have eq2 : x ≠ y := hxy
  have eq3 : x + y + p = 0 := by
    apply (mul_left_inj' (show (x - y) ≠ 0 by
      intro h
      apply hxy
      linarith
    )).mp
    linarith [eq1]
  have eq4 : (x - y) ^ 2 = 25 := by
    cases eq_or_eq_neg_of_abs_eq h1 with
    | inl h =>
      nlinarith
    | inr h =>
      nlinarith
  have eq5 : x * y = q := by
    have eq2' : x^2 + p * x + q = 0 := hx
    have eq3' : y^2 + p * y + q = 0 := hy
    have eq6 : x^2 + y^2 + p * (x + y) + 2 * q = 0 := by
      nlinarith [eq2', eq3']
    have eq7 : x + y = -p := by linarith [eq3]
    have eq8 : x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by
      linarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    rw [eq7] at eq8
    nlinarith
  have eq6 : p ^ 2 - 4 * q = 25 := by
    have h5 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
      linarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    rw [show (x + y) = -p by linarith [eq3]] at h5
    rw [show (x * y) = q by linarith [eq5]] at h5
    nlinarith [eq4, h5]
  -- From |x^3 - y^3|=35
  have eq7 : |x^3 - y^3| = 35 := h2
  have eq8 : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) := by
    ring
  have eq9 : |x^3 - y^3| = |(x - y) * (x^2 + x * y + y^2)| := by
    rw [eq8]
  have eq10 : |(x - y) * (x^2 + x * y + y^2)| = |x - y| * |x^2 + x * y + y^2| := by
    rw [abs_mul]
  have eq11 : |x - y| = 5 := by
    cases eq_or_eq_neg_of_abs_eq h1 with
    | inl h =>
      have : x - y = 5 := by linarith
      rw [this]
      norm_num
    | inr h =>
      have : x - y = -5 := by linarith
      rw [this]
      norm_num
  have eq12 : |x^2 + x * y + y^2| = 7 := by
    rw [eq10] at eq9
    rw [eq11] at eq9
    have : |x^2 + x * y + y^2| = 7 := by
      linarith [eq7, eq9]
    assumption
  have eq13 : x^2 + x * y + y^2 = p^2 - q := by
    have eq7' : x + y = -p := by linarith [eq3]
    have eq8' : x * y = q := by linarith [eq5]
    have eq9' : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by
      linarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    rw [eq7'] at eq9'
    have eq10' : x^2 + x * y + y^2 = (x^2 + y^2) + (x * y) := by
      linarith
    rw [eq10']
    rw [show x^2 + y^2 = p^2 - 2 * q by
        nlinarith [eq9', eq8']
      ]
    rw [show x * y = q by linarith [eq8']]
    all_goals linarith
  have eq14 : |p^2 - q| = 7 := by
    have eq15 : p^2 - q = x^2 + x * y + y^2 := by
      linarith [eq13]
    rw [eq15]
    linarith [eq12]
  cases' abs_cases (p^2 - q) with h3 h3 <;> 
    try { 
      cases' abs_cases (x^3 - y^3) with h4 h4 <;> 
        try { 
          cases' abs_cases (x - y) with h5 h5 <;> 
            try { 
              nlinarith 
            }
        }
    }
  <;> try { 
    have hp2 : p^2 = 1 := by
      nlinarith 
    have hp : p = 1 ∨ p = -1 := by 
      have : p^2 = 1 := by
        linarith
      rw [sq_eq_one_iff] at this
      assumption 
    cases' hp with hp1 hp1
    · 
      left 
      constructor 
      · linarith 
      · nlinarith 
    · 
      right 
      constructor 
      · linarith 
      · nlinarith 
  }