import Mathlib

open Real

theorem algebra_254911 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h : a^2 + b^2 = c^2) (h1 : c - b ≠ 1) (h2 : c + b ≠ 1) :
    logb (b + c) a + logb (c - b) a = 2 * logb (b + c) a * logb (c - b) a := by
  have h3 : 0 < b + c := by
    nlinarith
  have h5 : c > b := by
    nlinarith [sq_nonneg (c - b), sq_pos_of_pos ha, h]
  have h4 : 0 < c - b := by
    nlinarith
  have h6 : logb (b + c) a = log a / log (b + c) := by 
    field_simp [logb]
  have h7 : logb (c - b) a = log a / log (c - b) := by 
    field_simp [logb]
  rw [h6, h7]
  have h8 : log (b + c) ≠ 0 := by
    have h8 : b + c > 0 := by
      nlinarith
    have h9 : b + c ≠ 1 := by
      intro h10
      apply h2
      linarith
    have h10 : log (b + c) ≠ 0 := by
      have h10 : (b + c) > 0 := h8
      have h11 : (b + c) ≠ 1 := h9
      exact log_ne_zero_of_pos_of_ne_one h10 h11
    exact h10
  have h9 : log (c - b) ≠ 0 := by
    have h9 : 0 < c - b := by
      nlinarith [sq_nonneg (c - b), sq_pos_of_pos ha, h]
    have h10 : c - b ≠ 1 := by
      intro h11
      apply h1
      linarith
    have h11 : log (c - b) ≠ 0 := by
      have h11 : (c - b) > 0 := h9
      have h12 : (c - b) ≠ 1 := h10
      exact log_ne_zero_of_pos_of_ne_one h11 h12
    exact h11
  have h11 : log a * log (c - b) + log a * log (b + c) = 2 * (log a) ^ 2 := by
    have h14a : log (c - b) + log (b + c) = 2 * log a := by
      have h14b : (c - b) * (b + c) = a ^ 2 := by
        nlinarith 
      have h12a : log ((c - b) * (b + c)) = log (c - b) + log (b + c) := by
        rw [log_mul (by linarith) (by linarith)]
      have h13a : log ((c - b) * (b + c)) = 2 * log a := by
        calc 
          log ((c - b) * (b + c)) = log (a ^ 2) := by 
            rw [h14b]
          _ = 2 * log a := by 
            simp [log_pow]
      linarith [h12a, h13a]
    calc
      log a * log (c - b) + log a * log (b + c) = log a * (log (c - b) + log (b + c)) := by ring
      _ = log a * (2 * log a) := by rw [h14a]
      _ = 2 * (log a) ^ 2 := by ring
  have eq3 : log a / log (b + c) + log a / log (c - b) = (log a * log (c - b) + log a * log (b + c)) / (log (b + c) * log (c - b)) := by
    field_simp [h8, h9]
    <;> ring
  have eq4 : 2 * (log a / log (b + c)) * (log a / log (c - b)) = 2 * (log a) ^ 2 / (log (b + c) * log (c - b)) := by
    field_simp [h8, h9]
    <;> ring
  rw [eq3, eq4]
  rw [h11]
  all_goals
    field_simp [h8, h9]
    <;> ring