import Mathlib

theorem number_theory_283424 {n : ℕ} (P : Polynomial ℤ) (hP : P.degree = n)
    (hP1 : Odd (P.eval 0)) (hP2 : Odd (P.eval 1)) :
    ¬∃ x : ℤ, P.eval x = 0 := by
  intro h
  rcases h with ⟨x, hx⟩
  have h1 : (P.eval 0 : ℤ) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hP1
    omega
  have h2 : (P.eval 1 : ℤ) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hP2
    omega
  have h3 : ∀ (x : ℤ), (P.eval x : ℤ) % 2 = 1 := by
    intro x
    have h5 : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases h5 with (h5 | h5)
    · -- When x % 2 = 0
      have h6 : (x : ℤ) % 2 = 0 := h5
      have h14 : (P.eval x : ℤ) % 2 = (P.eval (0 : ℤ) : ℤ) % 2 := by
        have h15 : ((x - (0 : ℤ)) : ℤ) ∣ (P.eval x - P.eval (0 : ℤ)) := by
          apply P.sub_dvd_eval_sub
        have h17 : ((2 : ℤ)) ∣ (x - (0 : ℤ)) := by
          omega
        have h19 : ((2 : ℤ)) ∣ (P.eval x - P.eval (0 : ℤ)) := by
          exact dvd_trans h17 h15
        omega
      omega
    · -- When x % 2 = 1
      have h7 : (x : ℤ) % 2 = 1 := h5
      have h14 : (P.eval x : ℤ) % 2 = (P.eval (1 : ℤ) : ℤ) % 2 := by
        have h15 : ((x - (1 : ℤ)) : ℤ) ∣ (P.eval x - P.eval (1 : ℤ)) := by
          apply P.sub_dvd_eval_sub
        have h16 : ((2 : ℤ)) ∣ (x - (1 : ℤ)) := by
          omega
        have h19 : ((2 : ℤ)) ∣ (P.eval x - P.eval (1 : ℤ)) := by
          exact dvd_trans h16 h15
        omega
      omega
  have h4 : (P.eval x : ℤ) % 2 = 1 := h3 x
  omega