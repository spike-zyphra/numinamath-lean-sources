import Mathlib

theorem algebra_130644 {P : Polynomial ℤ} (hP : Odd (P.eval 0) ∧ Odd (P.eval 1)) :
    ¬∃ x : ℤ, P.eval x = 0 := by
  intro h
  rcases h with ⟨x, hx⟩
  have h1 : P.eval 0 % 2 = 1 := by 
    have h1 : Odd (P.eval 0) := hP.1
    obtain ⟨k, hk⟩ := h1
    omega
  have h2 : P.eval 1 % 2 = 1 := by
    have h2 : Odd (P.eval 1) := hP.2
    obtain ⟨k, hk⟩ := h2
    omega
  have h3 : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases h3 with (h3 | h3)
  · -- x is even
    have h5 : x % 2 = 0 := h3
    have h6 : (x - (0 : ℤ) : ℤ) ∣ (P.eval x - P.eval 0) := by
      apply P.sub_dvd_eval_sub
    obtain ⟨k, hk⟩ := h6
    have h9 : x * k = (P.eval x - P.eval 0) := by linarith [hk]
    have h10 : (x * k) % 2 = 0 := by
      simp [Int.mul_emod, h3]
      <;> omega
    have h11 : (P.eval x - P.eval 0) % 2 = 1 := by 
      omega
    omega
  · -- x is odd
    have h5 : x % 2 = 1 := h3
    have h7 : (x - (1 : ℤ) : ℤ) ∣ (P.eval x - P.eval 1) := by
      apply P.sub_dvd_eval_sub
    obtain ⟨k, hk⟩ := h7
    have h9 : (x - 1) * k = (P.eval x - P.eval 1) := by linarith [hk]
    have h10 : ((x - 1) * k) % 2 = 0 := by 
      have h55 : (x - 1) % 2 = 0 := by
        omega
      simp [Int.mul_emod, h55]
    have h11 : (P.eval x - P.eval 1) % 2 = 1 := by
      omega
    omega