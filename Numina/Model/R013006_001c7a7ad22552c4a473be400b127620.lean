import Mathlib

theorem number_theory_249653 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h : ∀ x y, x^(a + b) + y = x^a * y^b ↔ (x = 2 ∧ y = 4)) :
    (a, b) = (1, 1) := by
  have h1 := h 0 0
  have eq1 : (0 : ℕ) ^ (a + b) + (0 : ℕ) = (0 : ℕ) ^ a * (0 : ℕ) ^ b := by
    have h2 : a ≥ 1 := by linarith
    have h3 : b ≥ 1 := by linarith
    have h4 : a + b ≥ 2 := by linarith
    have h5 : (0 : ℕ) ^ (a + b) = 0 := by
      have h9 : ∀ (n : ℕ), n ≥ 1 → (0 : ℕ) ^ n = 0 := by
        intro n hn
        induction n with
        | zero => 
          exfalso 
          all_goals linarith 
        | succ n ih =>
          cases n with
          | zero => 
            simp 
          | succ n => 
            simp [pow_succ, pow_zero] at ih ⊢
            all_goals try { omega }
            all_goals try { nlinarith }
      have h9a : a + b ≥ 1 := by omega
      specialize h9 (a + b) h9a
      linarith
    have h6 : (0 : ℕ) ^ a = 0 := by 
      have h9 : ∀ (n : ℕ), n ≥ 1 → (0 : ℕ) ^ n = 0 := by 
        intro n hn
        induction n with
        | zero => 
          exfalso 
          all_goals linarith 
        | succ n ih =>
          cases n with
          | zero => 
            simp 
          | succ n => 
            simp [pow_succ, pow_zero] at ih ⊢
            all_goals try { omega }
            all_goals try { nlinarith }
      have h9a : a ≥ 1 := by omega
      specialize h9 a h9a
      linarith
    have h7 : (0 : ℕ) ^ b = 0 := by 
      have h9 : ∀ (n : ℕ), n ≥ 1 → (0 : ℕ) ^ n = 0 := by 
        intro n hn
        induction n with
        | zero => 
          exfalso 
          all_goals linarith 
        | succ n ih =>
          cases n with
          | zero => 
            simp 
          | succ n => 
            simp [pow_succ, pow_zero] at ih ⊢
            all_goals try { omega }
            all_goals try { nlinarith }
      have h9a : b ≥ 1 := by omega
      specialize h9 b h9a
      linarith
    calc 
      (0 : ℕ) ^ (a + b) + (0 : ℕ) = (0 : ℕ) + (0 : ℕ) := by rw [h5]
      _ = (0 : ℕ) := by omega
      _ = (0 : ℕ) ^ a * (0 : ℕ) ^ b := by rw [h6, h7]; all_goals norm_num 
  norm_num [eq1] at h1 
  all_goals 
    try { 
      exfalso 
      <;> try { 
        tauto 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        tauto 
      }
    }
    <;> try { 
      aesop 
      <;> try { 
        nlinarith 
      } 
    }
    <;> try { 
      tauto 
    }
    <;> try { 
      omega 
    }