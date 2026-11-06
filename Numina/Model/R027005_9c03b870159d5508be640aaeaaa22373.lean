import Mathlib

theorem number_theory_233748 (n : ℕ) (hn : n > 0) (h : n * 150 ≡ 0 [ZMOD 660]) :
    n ≥ 22 := by 
  rw [Int.ModEq] at h 
  have h1 : (↑n * 150 : Int) % 660 = 0 := by 
    simpa using h

  have h2 : (660 : Int) ∣ (↑n * 150 : Int) := by 
    exact Int.dvd_of_emod_eq_zero h1

  rcases h2 with ⟨k, hk⟩
  have eq1 : (↑n : Int) * 150 = 660 * k := by 
    linarith

  have eq2 : (↑n : Int) * 5 = 22 * k := by
    omega

  have h3 : (22 : Int) ∣ (↑n : Int) * 5 := by 
    use k 
    all_goals 
      linarith

  have h4 : (22 : Int) ∣ (↑n : Int) := by 
    have h5 : (22 : Int) ∣ (↑n * 5) := h3
    have h6 : IsCoprime (22 : Int) (5 : Int) := by 
      norm_num [Int.isCoprime_iff_gcd_eq_one]
    have h7 : (22 : Int) ∣ (↑n : Int) := by 
      apply h6.dvd_of_dvd_mul_right h5 
    assumption

  rcases h4 with ⟨m, hm⟩
  have hm_pos : (m : Int) > 0 := by
    by_contra h7
    push_neg at h7 
    have h_eq_zero : m ≤ 0 := by omega 
    have hm_eq_zero : m = 0 := by omega 
    rw [hm_eq_zero] at hm
    have h_eq_zero_n : (↑n : Int) = 0 := by nlinarith 
    have h_eq_zero_n_nat : n = 0 := by
      norm_cast at h_eq_zero_n ⊢
    linarith [show n > 0 by exact_mod_cast hn]

  have hn22 : n ≥ 22 := by 
    omega

  assumption