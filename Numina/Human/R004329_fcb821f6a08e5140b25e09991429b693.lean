import Mathlib

theorem algebra_253316
  {P : Polynomial ℤ}
  (hP1 : P.eval 2020 = 2021)
  (hP2 : P.eval 2021 = 2021) :
  ∀ x : ℤ, P.eval x ≠ 0 := by

  have h_even_odd : ∀ x : ℤ, (x % 2 = 0) → P.eval x % 2 = 1 := by
    intros x hx
    have h1: (x - 2020) ∣ P.eval x - P.eval 2020 := by
      apply Polynomial.sub_dvd_eval_sub

    have h2 : (x - 2020) % 2 = 0 := by
      omega

    have h3 : (P.eval x - P.eval 2020 : ℤ) % 2 = 0 := by
      obtain ⟨k, hk⟩ := h1
      have : k * (x - 2020) % 2 = 0 := by
        simp [Int.mul_emod, h2]
      have : k * (x - 2020) = P.eval x - P.eval 2020 := by
        nlinarith
      omega

    omega

  have h_odd_odd : ∀ x : ℤ, (x % 2 = 1) → P.eval x % 2 = 1 := by
    intro x hx
    have h1: (x - 2021) ∣ P.eval x - P.eval 2021 := by
      apply Polynomial.sub_dvd_eval_sub
    have h2 : (x - 2021) % 2 = 0 := by
      omega
    have h3 : (P.eval x - P.eval 2021 : ℤ) % 2 = 0 := by
      obtain ⟨k, hk⟩ := h1
      have : k * (x - 2021) % 2 = 0 := by
        simp [Int.mul_emod, h2]
      have : k * (x - 2021) = P.eval x - P.eval 2021 := by
        nlinarith
      omega
    omega


  intro x
  by_contra h
  mod_cases x % 2
  . have := h_even_odd x H
    rw [h] at this
    simp at this

  . have := h_odd_odd x H
    rw [h] at this
    simp at this
