import Mathlib

theorem number_theory_102631 (a : Fin 5 → ℤ) (b : ℤ)
    (h : ∑ i : Fin 5, a i ^ 2 = b ^ 2) :
    ¬ (∀ i : Fin 5, Odd (a i) ∧ Odd b) := by
  intro h1
  have h2 := h1 0
  have h3 := h1 1
  have h4 := h1 2
  have h5 := h1 3
  have h6 := h1 4
  rcases h2 with ⟨h_odd1, h_odd_b⟩
  rcases h3 with ⟨h_odd2, h_odd_b2⟩
  rcases h4 with ⟨h_odd3, h_odd_b3⟩
  rcases h5 with ⟨h_odd4, h_odd_b4⟩
  rcases h6 with ⟨h_odd5, h_odd_b5⟩
  have h7 : (a 0) % 8 = 1 ∨ (a 0) % 8 = 3 ∨ (a 0) % 8 = 5 ∨ (a 0) % 8 = 7 := by
    rcases h_odd1 with ⟨k, hk⟩
    omega
  have h8 : (a 1) % 8 = 1 ∨ (a 1) % 8 = 3 ∨ (a 1) % 8 = 5 ∨ (a 1) % 8 = 7 := by
    rcases h_odd2 with ⟨k, hk⟩
    omega
  have h9 : (a 2) % 8 = 1 ∨ (a 2) % 8 = 3 ∨ (a 2) % 8 = 5 ∨ (a 2) % 8 = 7 := by
    rcases h_odd3 with ⟨k, hk⟩
    omega
  have h10 : (a 3) % 8 = 1 ∨ (a 3) % 8 = 3 ∨ (a 3) % 8 = 5 ∨ (a 3) % 8 = 7 := by 
    rcases h_odd4 with ⟨k, hk⟩
    omega
  have h11 : (a 4) % 8 = 1 ∨ (a 4) % 8 = 3 ∨ (a 4) % 8 = 5 ∨ (a 4) % 8 = 7 := by 
    rcases h_odd5 with ⟨k, hk⟩
    omega
  have h12 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
    rcases h_odd_b with ⟨k, hk⟩
    omega
  have h13 : (a 0) ^ 2 % 8 = 1 := by 
    rcases h7 with (h7 | h7 | h7 | h7)
    all_goals
      simp [pow_two, Int.add_emod, Int.mul_emod, h7]
  have h14 : (a 1) ^ 2 % 8 = 1 := by 
    rcases h8 with (h8 | h8 | h8 | h8)
    all_goals 
      simp [pow_two, Int.add_emod, Int.mul_emod, h8]
  have h15 : (a 2) ^ 2 % 8 = 1 := by 
    rcases h9 with (h9 | h9 | h9 | h9)
    all_goals 
      simp [pow_two, Int.add_emod, Int.mul_emod, h9]
  have h16 : (a 3) ^ 2 % 8 = 1 := by 
    rcases h10 with (h10 | h10 | h10 | h10)
    all_goals 
      simp [pow_two, Int.add_emod, Int.mul_emod, h10]
  have h17 : (a 4) ^ 2 % 8 = 1 := by 
    rcases h11 with (h11 | h11 | h11 | h11)
    all_goals 
      simp [pow_two, Int.add_emod, Int.mul_emod, h11]
  have h18 : b ^ 2 % 8 = 1 := by 
    rcases h12 with (h12 | h12 | h12 | h12)
    all_goals 
      simp [pow_two, Int.add_emod, Int.mul_emod, h12]
  have h19 : (∑ i : Fin 5, a i ^ 2) % 8 = 5 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Int.add_emod, h13, h14, h15, h16, h17]
  have h20 : b ^ 2 % 8 = 5 := by
    omega
  omega