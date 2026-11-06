import Mathlib


open Nat


lemma lemma_1 (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
  (b : ℝ) (hb : b ≠ 0) (h : ((n : ℝ) * ((n : ℝ) - 1) / 2) * ((k : ℝ) ^ (n - 2)) * b ^ n =
    ((n : ℝ) * ((k : ℝ) ^ (n - 1))) * b ^ n) : ((n : ℝ) - 1) / 2 * ((k : ℝ) ^ (n - 2)) = (k : ℝ) ^ (n - 1) := by
  have h1 : ((n : ℝ) * ((n : ℝ) - 1) / 2) * ((k : ℝ) ^ (n - 2)) * b ^ n =
      ((n : ℝ) * ((k : ℝ) ^ (n - 1))) * b ^ n := h
  have hb_pow_ne_zero : b ^ n ≠ 0 := by
    apply pow_ne_zero
    exact hb
  have eq1 : ((n : ℝ) * ((n : ℝ) - 1) / 2) * ((k : ℝ) ^ (n - 2)) = (n : ℝ) * ((k : ℝ) ^ (n - 1)) := by
    apply (mul_left_inj' hb_pow_ne_zero).mp 
    linarith
  have hn' : (n : ℝ) ≠ 0 := by
    have hn1 : 2 ≤ n := by linarith
    have hn2 : n ≥ 2 := by linarith
    have hn3 : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hn1
    by_contra h0
    nlinarith
  have eq2 : ((n : ℝ) - 1) / 2 * ((k : ℝ) ^ (n - 2)) = (k : ℝ) ^ (n - 1) := by
    apply (mul_left_inj' hn').mp 
    linarith [eq1]
  exact eq2


theorem algebra_95886 {a b : ℝ} (n k:Nat) (hab : a*b ≠ 0) (twolen:2≤n) (kpos:0<k) (hk :a = k * b) (h:-(n.choose 1) * a^(n-1)* b + (n.choose 2) * a^(n-2) * b^2 = 0) : n = 2 * k + 1 := by
  have ha : a ≠ 0 := by
    by_contra ha
    have h1 : a * b = 0 := by 
      rw [ha]
      norm_num 
    contradiction 
  have hb : b ≠ 0 := by
    by_contra hb
    have h1 : a * b = 0 := by
      rw [hb]
      norm_num 
    contradiction 
  -- substitute a = k * b
  rw [hk] at h
  have hb_pow_ne_zero : (b : ℝ) ^ n ≠ 0 := by 
    apply pow_ne_zero
    exact hb 
  -- manipulate powers of b
  have h_eq : -(n.choose 1 : ℝ) * (k * b) ^ (n - 1) * b + (n.choose 2) * (k * b) ^ (n - 2) * b ^ 2 = (b ^ n) * (- (n.choose 1 : ℝ) * (k : ℝ) ^ (n-1) + (n.choose 2 : ℝ) * (k : ℝ) ^ (n - 2) ) := by
    have hn2 : n ≥ 2 := by linarith 
    induction n with 
    | zero => 
      exfalso <;> linarith 
    | succ n' => 
      cases n' with 
      | zero => 
        exfalso <;> linarith 
      | succ n'' => 
        simp [pow_succ, mul_pow, mul_assoc, pow_zero, mul_zero] 
        <;> ring 
  -- Common factor b^n 
  rw [h_eq] at h
  have heq : - (n.choose 1 : ℝ) * (k : ℝ) ^ (n - 1) + (n.choose 2 : ℝ) * (k : ℝ) ^ (n - 2) = 0 := by
    apply (mul_left_inj' hb_pow_ne_zero).mp
    linarith 
  have eq1 : (n.choose 1 : ℝ) = (n : ℝ) := by 
    simp [Nat.choose_one_right]
  
  have eq4 : (n.choose 2 : ℝ) = ((n : ℝ) * (n - 1 : ℝ) ) / 2 := by
    have h8 : ∀ n : Nat, (n.choose 2 : ℝ) = ((n : ℝ) * (n - 1 : ℝ) ) / 2 := by 
      intro n 
      induction n with
      | zero => 
        simp 
        <;> norm_num [Nat.choose_zero_right] 
        <;> norm_cast 
      | succ n ih => 
        cases n with 
        | zero => 
          norm_num [Nat.choose_zero_right, Nat.choose_succ_right]
          <;> norm_cast 
        | succ n' =>
          simp [Nat.choose_succ_right, mul_add, mul_zero, pow_succ, pow_one] at ih ⊢
          <;> norm_num at ih ⊢
          <;> norm_cast at ih ⊢ 
          <;> field_simp at ih ⊢ 
          <;> nlinarith
    specialize h8 n 
    norm_cast at h8 ⊢ 
    all_goals try { tauto } 
    all_goals try { nlinarith } 
    all_goals try { 
      cases n with 
      | zero => tauto 
      | succ m => 
        cases m with 
        | zero => tauto 
        | succ m =>
          norm_num 
          <;> nlinarith
    }
  -- completed eq4 - coefficient part
  
  rw [eq1, eq4] at heq 
  have hk_pos : (k : ℝ) > 0 := by 
    exact_mod_cast (show 0 < (k : ℕ) by omega)
  -- solving powers k^n 
  have h_eq1 : ((n : ℝ) * ((n : ℝ) - 1 : ℝ) ) / 2 * (k : ℝ) ^ (n - 2) = (n : ℝ) * (k : ℝ) ^ (n - 1 : ℕ) := by 
    nlinarith [heq]
  
  have h_eq3 : (k : ℝ) ^ (n - 1 : ℕ) = (k : ℝ) * (k : ℝ) ^ (n - 2 : ℕ) := by
    have hn2 : n ≥ 2 := by linarith
    have h11 : n - 1 = (n - 2 : ℕ) + 1 := by omega
    rw [h11] 
    simp [pow_succ, mul_assoc] 
    all_goals try { tauto }
    all_goals try { nlinarith }
    all_goals try { ring }
  
  rw [h_eq3] at h_eq1
  
  have hk1 : (k : ℝ) ^ (n - 2 : ℕ) > 0 := by positivity 
  have hk0 : (k : ℝ) ^ (n - 2 : ℕ) ≠ 0 := by positivity 
  have h_eq4 : ((n : ℝ) * ((n : ℝ) - 1 : ℝ) ) / 2 = (n : ℝ) * (k : ℝ) := by
    apply (mul_left_inj' hk0).mp 
    nlinarith [h_eq1]
  
  have h_eq6 : (n : ℝ) > 0 := by
    have hn11 : n > 0 := by omega
    have hn12 : (n : ℝ) > 0 := by exact_mod_cast hn11
    positivity
  
  -- dividing powers to solve (using direct assuming bread)
  have h_eq7 : ((n : ℝ) - 1 : ℝ) / 2 = (k : ℝ) := by
    apply (mul_left_inj' (show (n : ℝ) ≠ 0 by positivity )).mp
    field_simp at h_eq4 ⊢ 
    linarith
  
  have h_eq8 : (n : ℝ) = 2 * (k : ℝ) + 1 := by 
    linarith
  
  -- cast to the desired form 
  have h_eq9 : n = 2 * k + 1 := by
    exact_mod_cast h_eq8
  
  exact h_eq9