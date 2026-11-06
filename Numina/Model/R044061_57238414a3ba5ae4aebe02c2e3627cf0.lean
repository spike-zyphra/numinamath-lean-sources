import Mathlib

theorem number_theory_271166 (k : ℕ) :
    ¬∃ m n, m > 0 ∧ n > 0 ∧ m^2 + n^2 = 3^k := by 
  rintro ⟨m, n, hm, hn, h_eq⟩
  have h1 : m ^ 2 % 3 = 0 ∨ m ^ 2 % 3 = 1 := by
    have h1 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by 
      omega
    rcases h1 with (h1 | h1 | h1)
    · -- m ≡ 0 (mod 3)
      simp [pow_two, Nat.mul_mod, h1]
    · -- m ≡ 1 (mod 3)
      simp [pow_two, Nat.mul_mod, h1]
    · -- m ≡ 2 (mod 3)
      simp [pow_two, Nat.mul_mod, h1]
  have h2 : n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- n ≡ 0 (mod 3)
      simp [pow_two, Nat.mul_mod, h2]
    · -- n ≡ 1 (mod 3)
      simp [pow_two, Nat.mul_mod, h2]
    · -- n ≡ 2 (mod 3)
      simp [pow_two, Nat.mul_mod, h2]
  have h3 : k ≥ 1 := by
    by_contra h4
    push_neg at h4
    have : k = 0 := by 
      omega
    rw [this] at h_eq
    have h5 : m ^ 2 + n ^ 2 = 1 := by
      linarith
    nlinarith [sq_pos_of_pos hm, sq_pos_of_pos hn]
  have h4 : (m ^ 2 + n ^ 2) % 3 = 0 := by
    have h5 : k ≥ 1 := h3
    have h6 : (3 ^ k) % 3 = 0 := by
      have h5 : k ≥ 1 := by linarith
      have h6 : ∀ (k : ℕ), k ≥ 1 → (3 ^ k) % 3 = 0 := by 
        intro k hk
        induction k with 
        | zero => 
          exfalso; linarith
        | succ k ih =>
          cases k with
          | zero => 
            simp [Nat.pow_succ, Nat.mul_mod]
          | succ k => 
            simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
            all_goals 
              omega
      specialize h6 k h5
      simpa using h6
    have h7 : (m ^ 2 + n ^ 2) % 3 = (3 ^ k) % 3 := by 
      omega
    rw [h6] at h7
    omega
  -- This implies both $m$ and $n$ must be divisible by 3
  have h5 : m % 3 = 0 := by 
    by_contra h6
    push_neg at h6
    have h7 : m ^ 2 % 3 = 1 := by 
      have h8 : m % 3 = 1 ∨ m % 3 = 2 := by 
        omega
      rcases h8 with (h8 | h8)
      · -- m ≡ 1 (mod 3)
        simp [pow_two, Nat.mul_mod, h8]
      · -- m ≡ 2 (mod 3)
        simp [pow_two, Nat.mul_mod, h8]
    have h8 : n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := h2
    omega
  have h6 : n % 3 = 0 := by 
    by_contra h7
    push_neg at h7
    have h8 : n ^ 2 % 3 = 1 := by 
      have h9 : n % 3 = 1 ∨ n % 3 = 2 := by 
        omega
      rcases h9 with (h9 | h9)
      · -- n ≡ 1 (mod 3)
        simp [pow_two, Nat.mul_mod, h9]
      · -- n ≡ 2 (mod 3)
        simp [pow_two, Nat.mul_mod, h9]
    have h9 : m ^ 2 % 3 = 0 ∨ m ^ 2 % 3 = 1 := h1
    omega
  -- So, m and n are multiples of 3
  have h7 : ∃ a, m = 3 * a := by 
    refine' ⟨m / 3, by omega⟩
  -- So, m and n are multiples of 3
  have h8 : ∃ b, n = 3 * b := by 
    refine' ⟨n / 3, by omega⟩
  rcases h7 with ⟨a, ha⟩
  rcases h8 with ⟨b, hb⟩
  rw [ha] at h_eq 
  rw [hb] at h_eq
  have h9 : 9 * (a ^ 2 + b ^ 2) = 3 ^ k := by
    nlinarith 
  have ha0 : a > 0 := by 
    nlinarith [show a > 0 by nlinarith, sq_pos_of_pos hm]
  have hb0 : b > 0 := by 
    nlinarith [show b > 0 by nlinarith, sq_pos_of_pos hn]
  have h11 : k ≥ 2 := by
    by_contra h12
    push_neg at h12
    have h12' : k < 2 := by
      omega
    have h13 : k = 0 ∨ k = 1 := by 
      omega
    rcases h13 with (h13 | h13)
    · -- k = 0
      rw [show k = 0 by linarith] at h9
      norm_num at h9 
      all_goals 
        nlinarith [sq_pos_of_pos ha0, sq_pos_of_pos hb0]
    · -- k = 1
      rw [show k = 1 by linarith] at h9
      norm_num at h9 
      all_goals 
        nlinarith [sq_pos_of_pos ha0, sq_pos_of_pos hb0]
  -- This implies existence of solutions for lower k exponents - which is impossible.
  have h9' : a^2 + b^2 = 3 ^ (k - 2) := by
    have h20 : k ≥ 2 := h11 
    have eq1 : 9 * (a ^ 2 + b ^ 2) = 3 ^ k := h9
    have eq2 : 3 ^ k = 9 * (3 ^ (k - 2)) := by
      have h23 : k ≥ 2 := h20
      have h24 : k - 2 + 2 = k := by
        omega 
      calc 
        3 ^ k = 3 ^ (k - 2 + 2) := by rw [h24]
        _ = (3 ^ (k - 2)) * (3 ^ 2) := by 
          rw [Nat.pow_add]
        _ = 9 * (3 ^ (k - 2)) := by 
          ring_nf
    rw [eq2] at eq1
    omega 
  -- Recursive inductive step of the theorem
  have h14 : ∃ m n, m > 0 ∧ n > 0 ∧ m^2 + n^2 = 3 ^ (k - 2) := by
    refine' ⟨a, b, by nlinarith, by nlinarith, by nlinarith [h9']⟩
  -- Now this existence contradicts the theorem at k-2
  have h13 : ¬ ∃ m n, m > 0 ∧ n > 0 ∧ m^2 + n^2 = 3 ^ (k - 2) := by 
    apply number_theory_271166 
  exfalso
  exact h13 h14