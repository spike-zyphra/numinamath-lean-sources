import Mathlib

theorem number_theory_286686 (a : Fin 5 → ℤ) (b : ℤ)
    (h : ∑ i : Fin 5, a i ^ 2 = b ^ 2) :
    ¬ (∀ i : Fin 5, Odd (a i) ∧ Odd b) := by 
  intro h1 
  have h1' : ∀ i : Fin 5, (a i : ℤ) % 2 = 1 ∧ Odd b := by 
    intro i 
    have h2 := h1 i 
    constructor 
    · -- Show that a_i is odd 
      have h11 : Odd (a i) := (h2).1 
      have odd_eq : (a i : ℤ) % 2 = 1 := by 
        obtain ⟨k, hk⟩ := h11 
        omega 
      tauto 
    · -- Show that b is odd 
      tauto 
  have h14 : ∀ i : Fin 5, (a i : ℤ) % 8 = 1 ∨ (a i : ℤ) % 8 = 3 ∨ (a i : ℤ) % 8 = 5 ∨ (a i : ℤ) % 8 = 7 := by
    intro i 
    have h11 : (a i : ℤ) % 2 = 1 := (h1' i).1 
    omega 
  have eq5 : (∑ i : Fin 5, a i ^ 2 : ℤ) % 8 = 5 := by
    have h14' : ∀ i : Fin 5, (a i ^ 2 : ℤ) % 8 = 1 := by 
      intro i 
      have h14i : (a i : ℤ) % 8 = 1 ∨ (a i : ℤ) % 8 = 3 ∨ (a i : ℤ) % 8 = 5 ∨ (a i : ℤ) % 8 = 7 := h14 i 
      rcases h14i with (h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    have eq6 : (∑ i : Fin 5, a i ^ 2) % 8 = 5 := by 
      have h2 : (∑ i : Fin 5, a i ^ 2) % 8 = (∑ i : Fin 5, (a i ^ 2 % 8)) % 8 := by 
        simp [Finset.sum_int_mod]
      rw [h2] 
      rw [Finset.sum_congr rfl (fun i _ => h14' i)]
      all_goals 
        simp [Finset.sum_const, Finset.card_fin]
    exact eq6 
  have eq1 : (b : ℤ) % 8 = 1 ∨ (b : ℤ) % 8 = 3 ∨ (b : ℤ) % 8 = 5 ∨ (b : ℤ) % 8 = 7 := by
    have h1a : Odd b := by
      have h2a := h1 0 
      tauto 
    have : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
      rcases h1a with ⟨k, hk⟩
      omega 
    assumption 
  have eq4 : (b ^ 2 : ℤ) % 8 = 1 := by
    rcases eq1 with (h1a | h1a | h1a | h1a) <;> 
      simp [h1a, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod]
  have h_eq1 : (∑ i : Fin 5, a i ^ 2 : ℤ) = (b ^ 2 : ℤ) := by
    simpa using h 
  have eq6 : (∑ i : Fin 5, a i ^ 2 : ℤ) % 8 = (b^2 : ℤ) % 8 := by 
    rw [h_eq1] 
  have eq7 : (5 : ℤ) = (1 : ℤ) := by 
    omega 
  omega