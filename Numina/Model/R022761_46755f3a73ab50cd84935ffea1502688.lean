import Mathlib

theorem number_theory_110825 (A : ℕ → ℤ) (hA : ∀ n, A n = 2016 ^ n + 2015 ^ n + 64 ^ n) :
    ∀ n, Odd n → 91 ∣ A n := by 
  intro n hn 
  rw [hA n]
  have h2 : n % 2 = 1 := by 
    rcases hn  with ⟨k, hk⟩ 
    omega 
  have h5 : (2016 : ℤ) ^ n + (2015 : ℤ) ^ n + (64 : ℤ) ^ n ≡ 0 [ZMOD 7] := by 
    have h6 : n % 2 = 1 := h2 
    have h7 : (2016 : ℤ) % 7 = 0 := by norm_num 
    have h8 : (2015 : ℤ) % 7 = 6 := by norm_num 
    have h9 : (64 : ℤ) % 7 = 1 := by norm_num 
    have h6n : n > 0 := by 
      rcases hn  with ⟨k, hk⟩ 
      omega 
    have h11 : (2016 : ℤ) ^ n % 7 = 0 := by
      have : n > 0 := by 
        rcases hn  with ⟨k, hk⟩ 
        omega 
      have h12 : ∀ k > 0, (2016 : ℤ) ^ k % 7 = 0 := by 
        intro k hk 
        induction k  with 
        | zero => linarith 
        | succ k ih =>
          cases k  with 
          | zero => 
            simp [h7] 
          | succ k =>
            simp [pow_succ, pow_mul, h7] at ih ⊢ 
            all_goals omega 
      specialize h12 n (by linarith) 
      simpa using h12 
    have h14 : (2015 : ℤ) ^ n % 7 = 6 := by
      have h8 : (2015 : ℤ) % 7 = 6 := by norm_num 
      have h6n : n % 2 = 1 := h2 
      have : n > 0 := by 
        rcases hn  with ⟨k, hk⟩ 
        omega 
      have h15 : n % 2 = 1 := h6n 
      have h12 : ∀ k : ℕ, (2015 : ℤ) ^ (2 * k + 1) % 7 = 6 := by 
        intro k 
        induction k  with 
        | zero =>
          norm_num 
        | succ k ih =>
          simp [pow_succ, pow_mul, h8] at ih ⊢ 
          all_goals omega 
      have : ∃ k : ℕ, n = 2 * k + 1 := by 
        refine ⟨(n - 1) / 2, by 
          omega 
        ⟩ 
      rcases this  with ⟨k, hk⟩ 
      specialize h12 k 
      rw [hk] at *
      omega 
    have h16 : (64 : ℤ) ^ n % 7 = 1 := by 
      have h9 : (64 : ℤ) % 7 = 1 := by norm_num 
      have h6n : n > 0 := by 
        rcases hn  with ⟨k, hk⟩ 
        omega 
      have h17 : ∀ k > 0, (64 : ℤ) ^ k % 7 = 1 := by 
        intro k hk 
        induction k  with 
        | zero => linarith 
        |  succ k ih =>
          cases k  with 
          | zero => 
            simp [h9] 
          | succ k =>
            simp [pow_succ, pow_mul, h9] at ih ⊢ 
            all_goals omega 
      specialize h17 n (by linarith) 
      simpa using h17 
    show (2016 : ℤ) ^ n + (2015 : ℤ) ^ n + (64 : ℤ) ^ n ≡ 0 [ZMOD 7]
    simp [Int.ModEq, Int.add_emod, h11, h14, h16] 
  have h6 : (2016 : ℤ) ^ n + (2015 : ℤ) ^ n + (64 : ℤ) ^ n ≡ 0 [ZMOD 13] := by 
    have h10 : (2016 : ℤ) % 13 = 1 := by norm_num 
    have h11 : (2015 : ℤ) % 13 = 0 := by norm_num 
    have h12 : (64 : ℤ) % 13 = 12 := by norm_num 
    have h6n : n > 0 := by 
      rcases hn  with ⟨k, hk⟩ 
      omega 
    have h13 : (2016 : ℤ) ^ n % 13 = 1 := by 
      have : n > 0 := by 
        rcases hn  with ⟨k, hk⟩ 
        omega 
      have h100 : ∀ k > 0, (2016 : ℤ) ^ k % 13 = 1 := by 
        intro k hk 
        (induction k  with 
        | zero => linarith 
        | succ k ih =>
          cases k  with 
          | zero => 
            simp [h10] 
          | succ k =>
            simp [pow_succ, pow_mul, h10] at ih ⊢ 
            all_goals omega 
        ) 
      specialize h100 n (by linarith) 
      simpa using h100 
    have h14 : (2015 : ℤ) ^ n % 13 = 0 := by 
      have h111 : (2015 : ℤ) % 13 = 0 := by norm_num 
      have h6n : n > 0 := by 
        rcases hn  with ⟨k, hk⟩ 
        omega 
      have h1111 : ∀ k > 0, (2015 : ℤ) ^ k % 13 = 0 := by 
        intro k hk 
        induction k  with 
        | zero => linarith 
        | succ k ih =>
          cases k  with 
          | zero => 
            simp [h111] 
          | succ k =>
            simp [pow_succ, pow_mul, h111] at ih ⊢ 
            all_goals omega 
      specialize h1111 n (by linarith) 
      simpa using h1111 
    have h15 : (64 : ℤ) ^ n % 13 = 12 := by 
      have h6n : n % 2 = 1 := h2 
      have : n > 0 := by 
        rcases hn  with ⟨k, hk⟩ 
        omega 
      have h16n : ∃ k : ℕ, n = 2 * k + 1 := by 
        refine ⟨(n - 1) / 2, by 
          omega 
        ⟩ 
      rcases h16n with ⟨k, h17n⟩ 
      have h18 : ∀ k : ℕ, (64 : ℤ) ^ (2 * k + 1) % 13 = 12 := by 
        intro k 
        induction k  with 
        | zero => 
          norm_num 
        | succ k ih =>
          have h90 : (64 : ℤ) ^ (2 * (k + 1) + 1) % 13 = 12 := by 
            have h41 : (64 : ℤ) ^ (2 * (k + 1) + 1) = (64 : ℤ) ^ (2 * k + 1) * (64 : ℤ) ^ 2 := by 
              ring_nf 
            rw [h41] 
            have h42 : ( (64 : ℤ) ^ (2 * k + 1) * (64 : ℤ) ^ 2 ) % 13 = 12 := by 
              have h43 : ( (64 : ℤ) ^ (2 * k + 1) * (64 : ℤ) ^ 2 ) % 13 = ( (64 : ℤ) ^ (2 * k + 1) % 13 ) * ( (64 : ℤ) ^ 2 % 13 ) % 13 := by 
                simp [Int.mul_emod] 
              rw [h43] 
              have h44 : (64 : ℤ) ^ (2 * k + 1) % 13 = 12 := by 
                exact_mod_cast ih 
              have h45 : (64 : ℤ) ^ 2 % 13 = 1 := by 
                norm_num 
              rw [h44, h45] 
              all_goals omega 
            exact_mod_cast h42 
          exact_mod_cast h90 
      specialize h18 k 
      rw [h17n] 
      all_goals omega 
    show (2016 : ℤ) ^ n + (2015 : ℤ) ^ n + (64 : ℤ) ^ n ≡ 0 [ZMOD 13]
    simp [Int.ModEq, Int.add_emod, h13, h14, h15] 
  norm_num [Int.ModEq] at h5 h6 ⊢ 
  omega