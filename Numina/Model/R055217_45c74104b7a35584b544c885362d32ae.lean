import Mathlib

theorem algebra_320680 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a ^ 3 + b ^ 3 + c ^ 3 = 0) :
    a ^ 15 + b ^ 15 + c ^ 15 = 0 := by 
  have h2 : a * b * c = 0 := by
    have h2 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + a * c + b * c)) := by
      ring
    rw [h₀] at h2
    nlinarith 
  cases' (mul_eq_zero.mp h2) with h2a h2bc
  · cases' (mul_eq_zero.mp h2a) with h2a1 h2a2
    · -- Case $a = 0$
      have ha0 : a = 0 := by 
        linarith 
      rw [ha0] 
      -- Then, $b + c = 0$
      have hbc0 : b + c = 0 := by 
        linarith 
      have h_eq : b ^ 15 + c ^ 15 = 0 := by 
        have h3 : b + c = 0 := hbc0 
        have h4 : c = -b := by linarith 
        rw [h4] 
        -- Polynomial x^n + (-x)^n = 0 for odd n
        have : b ^ 15 + (-b) ^ 15 = 0 := by 
          ring 
        linarith 
      -- The result follows 
      linarith [h_eq] 
    · -- Case $b = 0$
      have hb0 : b = 0 := by 
        linarith 
      rw [hb0] 
      -- Then, $a + c = 0$
      have hac0 : a + c = 0 := by 
        linarith 
      have h_eq : a ^ 15 + c ^ 15 = 0 := by 
        have h3 : a + c = 0 := hac0 
        have h4 : c = -a := by linarith 
        rw [h4] 
        -- Polynomial x^n + (-x)^n = 0 for odd n
        have : a ^ 15 + (-a) ^ 15 = 0 := by 
          ring 
        linarith 
      -- The result follows 
      linarith [h_eq] 
  · -- Case $c = 0$
    have hc0 : c = 0 := by 
      linarith 
    rw [hc0] 
    -- Then, $a + b = 0$
    have hab0 : a + b = 0 := by 
      linarith 
    have h_eq : a ^ 15 + b ^ 15 = 0 := by 
      have h3 : a + b = 0 := hab0 
      have h4 : b = -a := by linarith 
      rw [h4] 
      -- Polynomial x^n + (-x)^n = 0 for odd n
      have : a ^ 15 + (-a) ^ 15 = 0 := by 
        ring 
      linarith 
    -- The result follows 
    linarith [h_eq] 
  all_goals try { nlinarith } 
  all_goals try { ring_nf <;> nlinarith } 
  all_goals try { linarith }
  <;> nlinarith 
  <;> try { tauto } 
  <;> try { linarith } 
  <;> try { nlinarith }
  <;> try { tauto } 
  <;> try { linarith } 
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { linarith }
  <;> try { nlinarith }
  <;> try { linarith }
  <;> try { nlinarith }
  <;> try { linarith }
  <;> try { nlinarith }
  <;> try { linarith }
  all_goals try { ring_nf <;> nlinarith } <;> try { nlinarith }