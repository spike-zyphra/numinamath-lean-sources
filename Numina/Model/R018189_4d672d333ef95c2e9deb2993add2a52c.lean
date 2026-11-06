import Mathlib

theorem number_theory_255529 {f : Polynomial ℤ} (hf : f.eval 0 % 2 = 1 ∧ f.eval 1 % 2 = 1) :
    ¬∃ x : ℤ, f.eval x = 0 := by 
  intro h
  rcases h with ⟨x, hx⟩ 
  have h1 : f.eval 0 % 2 = 1 := hf.1
  have h2 : f.eval 1 % 2 = 1 := hf.2
  have h3 : x % 2 = 0 ∨ x % 2 = 1 := by 
    omega 
  rcases h3 with (h3 | h3)
  · -- x is even 
    have h4 : (f.eval x) % 2 = (f.eval 0) % 2 := by 
      have h5 : x % 2 = 0 := h3 
      have h6 : ∀ k : ℕ, (x ^ k) % 2 = (0 ^ k) % 2 := by
        intro k
        induction k with 
        | zero => 
          simp 
        | succ k ih => 
          simp [pow_succ, Int.add_emod, Int.mul_emod, h5] at ih ⊢ 
          all_goals try omega 
          <;> try nlinarith 
          <;> try tauto 
      have h7 : ∀ k : ℕ, (f.coeff k * x ^ k) % 2 = (f.coeff k * 0 ^ k) % 2 := by
        intro k
        have h8 : (x ^ k) % 2 = (0 ^ k) % 2 := h6 k 
        have h9 : (f.coeff k * x ^ k) % 2 = (f.coeff k * 0 ^ k) % 2 := by 
          simp [Int.mul_emod, h8] 
          all_goals try omega 
          <;> try nlinarith 
          <;> try tauto 
        tauto 
      simp [Polynomial.eval_eq_sum_range, Finset.sum_int_mod, h7]
      all_goals try nlinarith 
      <;> try tauto 
      <;> try all_goals omega 
      <;> try nlinarith 
      <;> try tauto 
      <;> tauto 
    rw [hx] at h4 
    omega 
  · -- x is odd 
    have h5 : x % 2 = 1 := h3 
    have h7 : ∀ k : ℕ, (x ^ k) % 2 = (1 ^ k) % 2 := by
      intro k
      induction k with 
      | zero => 
        simp 
      | succ k ih => 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h5] at ih ⊢ 
        all_goals try omega 
        <;> try nlinarith 
        <;> try tauto 
    have h8 : ∀ k : ℕ, (f.coeff k * x ^ k) % 2 = (f.coeff k * 1 ^ k) % 2 := by
      intro k
      have h9 : (x ^ k) % 2 = (1 ^ k) % 2 := h7 k 
      have h10 : (f.coeff k * x ^ k) % 2 = (f.coeff k * 1 ^ k) % 2 := by 
        simp [Int.mul_emod, h9]
        all_goals try omega 
        <;> try nlinarith 
        <;> try tauto 
        <;> try all_goals tauto 
      tauto 
    have h9 : (f.eval x) % 2 = (f.eval 1) % 2 := by 
      simp [Polynomial.eval_eq_sum_range, Finset.sum_int_mod, h8]
      all_goals try nlinarith 
      <;> try tauto 
      <;> try all_goals omega 
      <;> try nlinarith 
      <;> try tauto 
      <;> tauto 
    rw [hx] at h9 
    omega