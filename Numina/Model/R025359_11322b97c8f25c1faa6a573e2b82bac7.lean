import Mathlib

theorem algebra_182353 {a b : ℕ} (ha : a > 0) (hb : b > 0)
    (h : a / b = 57 ∧ a % b = 52) (h' : a / (b - 10) = 17380) :
    a / b = 20800 / 364 := by 
  have h1 : a / b = 57 := h.1
  have h2 : a % b = 52 := h.2
  have h3 : a = 57 * b + 52 := by 
    rw [←Nat.div_add_mod a b]
    rw [h1, h2]
    all_goals omega
  -- Show that b ≥ 11 to ensure b - 10 > 0 for the second division
  have h4 : b ≥ 11 := by 
    by_contra h5
    push_neg at h5
    have h6 : b ≤ 10 := by omega
    have h7 : b - 10 = 0 := by 
      omega
    rw [h7] at h'
    norm_num at h' 
    all_goals omega
  -- Equation from second division
  have h8 : a % (b - 10) < (b - 10 : ℕ) := by 
    apply Nat.mod_lt 
    omega
  have h9 : a = (b - 10) * (a / (b - 10)) + (a % (b - 10)) := by 
    rw [Nat.div_add_mod a (b - 10)]
    all_goals omega
  rw [h'] at h9
  -- Substitute a = 57 * b + 52 into the equation from second division
  have h11 : 57 * b + 52 = (b - 10) * 17380 + (a % (b - 10)) := by
    omega
  -- Apply the inequality from the modulus
  have h12 : a % (b - 10) < (b - 10 : ℕ) := h8
  -- Use omega to find a contradiction in the constraints.
  have h13 : b ≤ 20 := by 
    omega
  interval_cases b <;> omega
  all_goals omega