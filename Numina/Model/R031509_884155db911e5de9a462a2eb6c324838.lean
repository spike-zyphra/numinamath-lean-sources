import Mathlib

theorem algebra_178021 {m n : ℝ} (h1 : ∀ x, (x^2 + m * x + n) % (x - m) = m)
    (h2 : ∀ x, (x^2 + m * x + n) % (x - n) = n) :
    m = 0 ∧ n = 0 ∨ m = 0.5 ∧ n = 0 ∨ m = 1 ∧ n = -1 := by
  have eq1 := h1 m
  have eq2 := h2 n 
  simp [show m - m = (0 : ℝ) by ring, show m ^ 2 + m * m + n = 2 * m ^ 2 + n by ring] at eq1 
  simp [show n - n = (0 : ℝ) by ring, show n ^ 2 + m * n + n = n ^ 2 + m * n + n by ring] at eq2 
  have eq3 : 2 * m ^ 2 + n = m := by nlinarith 
  have eq4 : n ^ 2 + m * n = 0 := by 
    nlinarith 
  have h3 : n = m - 2 * m ^ 2 := by linarith 
  rw [h3] at eq4 
  have eq5 : m * (1 - 2 * m) * (2 * m) * (1 - m) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq5) with h6 h7
  · cases' (mul_eq_zero.mp h6) with h6 h6
    · cases' (mul_eq_zero.mp h6) with h6 h6
      · -- $m * (1-2 * m) * (2*m) * (1 -m) =0$ where first term is m =0
        left
        constructor
        · linarith
        · -- n = m - 2*m^2 from 0
          nlinarith
      · -- second term is 1 -2m  =0 then m =0.5
        right
        left
        -- 1 -2m =0 => m =0.5
        have hm : m = 0.5 := by nlinarith
        constructor 
        · linarith 
        · -- 0.5 - 2*(0.5)^2
          nlinarith
    · -- third term is 2m =0 => m =0 
      left 
      constructor 
      · nlinarith 
      · nlinarith 
  · -- fourth term: 1 -m =0 => m =1 
    right 
    right 
    have hm : m = 1 := by nlinarith 
    constructor 
    · linarith 
    · -- n =1 - 2*(1)^2
      nlinarith