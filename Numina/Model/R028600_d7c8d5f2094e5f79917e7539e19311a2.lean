import Mathlib

theorem negated_number_theory_48310 (P : Polynomial ℤ)
    (n : ℤ)
    (m : ℤ)
    (hP : P.eval n = m)
    (hm : m ≠ 10) :
    ∀ k : ℤ, m ∣ P.eval (n + k * m) := by
  intro k 
  have h1 : k * m ∣ (P.eval (n + k * m) - m) := by 
    have h2 : (n + k * m - n : ℤ) ∣ (P.eval (n + k * m) - P.eval n) := by 
      apply Polynomial.sub_dvd_eval_sub 
    have h4 : n + k * m - n = k * m := by 
      ring_nf 
    have h5 : P.eval n = m := hP 
    rw [h4] at h2 
    rw [h5] at h2 
    exact h2 
  have h3 : m ∣ (P.eval (n + k * m) - m) := by 
    have h4 : m ∣ k * m := by 
      use k 
      all_goals ring_nf 
    have h5 : k * m ∣ (P.eval (n + k * m) - m) := h1 
    exact dvd_trans h4 h5 
  have h7 : m ∣ m := by 
    simp 
  have h8 : m ∣ P.eval (n + k * m) := by 
    -- P(n + k*m) = (P(n + k*m) - m) + m
    have h9 : P.eval (n + k * m) = (P.eval (n + k * m) - m) + m := by 
      linarith 
    rw [h9] 
    apply dvd_add 
    exact h3 
    exact h7 
  exact h8