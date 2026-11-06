import Mathlib

theorem algebra_8055 {a b : ℤ} (ha : a > b) (hb : 0 ≤ b) (h : a * b + a + b = 2) :
    a = 2 ∧ b = 0 := by
  have h1 : a * b + a + b = 2 := h
  have h2 : a + 1 > b + 1 := by linarith 
  have h3 : (a + 1) * (b + 1) = 3 := by
    nlinarith 
  have h4 : a + 1 ∣ 3 := by 
    use b + 1 
    nlinarith 
  have h5 : a + 1 > 0 := by 
    nlinarith [show b ≥ 0 by linarith, show b + 1 ≥ 1 by linarith] 
  have h6 : a + 1 ≤ 3 := by 
    apply Int.le_of_dvd (by omega) h4 
  have : (a + 1) = 1 ∨ (a + 1) = 3 := by 
    interval_cases h7 : a + 1 <;> omega 
  cases this with 
  | inl h_eq_1 =>
    -- If $a + 1 = 1$, then $a = 0$ and $(a + 1)(b + 1) = 1 \cdot (b + 1) = 3$ implies $b + 1 = 3$, so $b = 2$
    -- But then $a = 0 > b = 2$ would be false
    exfalso 
    nlinarith 
  | inr h_eq_3 =>
    -- If $a + 1 = 3$, then $a = 2$ and $(a + 1)(b + 1) = 3 \cdot (b + 1) = 3$ implies $b + 1 = 1$, so $b = 0$
    -- This gives $a = 2 > b = 0$, which is valid
    have ha_eq_2 : a + 1 = 3 := by linarith 
    have hb_eq_1 : b + 1 = 1 := by 
      nlinarith 
    constructor 
    · -- Show that $a = 2$
      linarith 
    · -- Show that $b = 0$
      linarith