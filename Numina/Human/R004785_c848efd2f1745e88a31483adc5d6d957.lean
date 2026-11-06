import Mathlib

lemma lemma_6 (n m : ℕ) (sh : (n - m) % 4 = 0 ∧ 3 ^ (n - m) % 25 = 1) : (n - m) % 20 = 0 := by
  have h₇ : (n - m) % 20 = 0 := by
    have h₇₁ : (n - m) % 4 = 0 := sh.1
    have h₇₂ : 3 ^ (n - m) % 25 = 1 := sh.2
    -- We need to show that (n - m) % 20 = 0.
    -- The order of 3 modulo 25 is 20, so 3^k ≡ 1 mod 25 implies k % 20 = 0.
    have h₇₃ : (n - m) % 20 = 0 := by
      -- Use the fact that the order of 3 modulo 25 is 20.
      have h₇₄ : ∀ k : ℕ, 3 ^ k % 25 = 1 → k % 20 = 0 := by
        intro k hk
        -- The order of 3 modulo 25 is 20.
        have h₇₅ : k % 20 = 0 := by
          rw [← Nat.mod_add_div k 20] at hk
          -- Simplify the expression using properties of powers and modular arithmetic.
          have h₇₆ : 3 ^ (k % 20 + 20 * (k / 20)) % 25 = 1 := by simpa [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] using hk
          have h₇₇ : 3 ^ (k % 20) % 25 = 1 := by
            have h₇₈ : 3 ^ 20 % 25 = 1 := by norm_num
            have h₇₉ : 3 ^ (k % 20 + 20 * (k / 20)) % 25 = (3 ^ (k % 20) * (3 ^ 20) ^ (k / 20)) % 25 := by
              rw [pow_add, pow_mul]
              <;> simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod]
            rw [h₇₉] at h₇₆
            have h₈₀ : (3 ^ (k % 20) * (3 ^ 20) ^ (k / 20)) % 25 = 1 := by simpa using h₇₆
            have h₈₁ : (3 ^ (k % 20) * (3 ^ 20) ^ (k / 20)) % 25 = (3 ^ (k % 20) % 25 * ((3 ^ 20) ^ (k / 20) % 25)) % 25 := by
              simp [Nat.mul_mod]
            rw [h₈₁] at h₈₀
            have h₈₂ : (3 ^ 20) ^ (k / 20) % 25 = 1 := by
              have h₈₃ : 3 ^ 20 % 25 = 1 := by norm_num
              have h₈₄ : (3 ^ 20) ^ (k / 20) % 25 = 1 := by
                rw [← Nat.mod_add_div ((3 ^ 20) ^ (k / 20)) 25]
                simp [h₈₃, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
              exact h₈₄
            rw [h₈₂] at h₈₀
            have h₈₅ : (3 ^ (k % 20) % 25 * 1) % 25 = 1 := by simpa using h₈₀
            have h₈₆ : 3 ^ (k % 20) % 25 = 1 := by
              omega
            exact h₈₆
          have h₈₇ : k % 20 = 0 := by
            -- Check all possible values of k % 20 to see when 3 ^ (k % 20) % 25 = 1.
            have h₈₈ : k % 20 = 0 ∨ k % 20 = 1 ∨ k % 20 = 2 ∨ k % 20 = 3 ∨ k % 20 = 4 ∨ k % 20 = 5 ∨ k % 20 = 6 ∨ k % 20 = 7 ∨ k % 20 = 8 ∨ k % 20 = 9 ∨ k % 20 = 10 ∨ k % 20 = 11 ∨ k % 20 = 12 ∨ k % 20 = 13 ∨ k % 20 = 14 ∨ k % 20 = 15 ∨ k % 20 = 16 ∨ k % 20 = 17 ∨ k % 20 = 18 ∨ k % 20 = 19 := by omega
            rcases h₈₈ with (h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈ | h₈₈) <;>
              simp [h₈₈, pow_add, pow_one, Nat.pow_mod, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at h₇₇ ⊢ <;>
                omega
          exact h₈₇
        exact h₇₅
      have h₇₅ : (n - m) % 20 = 0 := h₇₄ (n - m) h₇₂
      exact h₇₅
    exact h₇₃
  assumption

lemma lemma_5 (k : ℕ) (hk : 3 ^ k % 5 = 1) : 3 ^ (k % 4) % 5 = 1 := by
  have h1 : k % 4 = 0 := by
    have h2 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
      omega
    rcases h2 with (h | h | h | h)
    · omega
    · -- If k % 4 = 1, then 3 ^ k % 5 = 3
      have h3 : k % 4 = 1 := h
      have h4 : 3 ^ k % 5 = 3 := by
        have h5 : k % 4 = 1 := h3
        have h6 : ∀ m, 3 ^ (4 * m + 1) % 5 = 3 := by
          intro m
          induction m with
          | zero =>
            simp
          | succ m ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals omega
        have h7 : k = 4 * (k / 4) + 1 := by
          omega
        rw [h7] at *
        apply h6 (k / 4)
      omega
    · -- If k % 4 = 2, then 3 ^ k % 5 = 4
      have h3 : k % 4 = 2 := h
      have h4 : 3 ^ k % 5 = 4 := by
        have h5 : k % 4 = 2 := h3
        have h6 : ∀ m, 3 ^ (4 * m + 2) % 5 = 4 := by
          intro m
          induction m with
          | zero =>
            simp
          | succ m ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals omega
        have h7 : k = 4 * (k / 4) + 2 := by
          omega
        rw [h7] at *
        apply h6 (k / 4)
      omega
    · -- If k % 4 = 3, then 3 ^ k % 5 = 2
      have h3 : k % 4 = 3 := h
      have h4 : 3 ^ k % 5 = 2 := by
        have h5 : k % 4 = 3 := h3
        have h6 : ∀ m, 3 ^ (4 * m + 3) % 5 = 2 := by
          intro m
          induction m with
          | zero =>
            simp
          | succ m ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals omega
        have h7 : k = 4 * (k / 4) + 3 := by
          omega
        rw [h7] at *
        apply h6 (k / 4)
      omega
  have h2 : 3 ^ (k % 4) % 5 = 1 := by
    simp [h1]
  exact h2

lemma lemma_4 (n m : ℕ) (h₄ : n - m ≥ 1) (h₆ : 1978 ^ (n - m) % 125 = 1) :
  (n - m) % 4 = 0 ∧ 3 ^ (n - m) % 25 = 1 := by
  have h₁ : (n - m) % 4 = 0 := by
    have h₁₁ : (1978 ^ (n - m) : ℕ) % 5 = 1 := by
      have h₁₂ : (1978 ^ (n - m) : ℕ) % 125 = 1 := by simpa using h₆
      have h₁₃ : (1978 ^ (n - m) : ℕ) % 5 = 1 := by
        have h₁₄ : (1978 ^ (n - m) : ℕ) % 5 = (1 : ℕ) % 5 := by
          have h₁₅ : (1978 ^ (n - m) : ℕ) % 125 = 1 := h₁₂
          have h₁₆ : (1978 ^ (n - m) : ℕ) % 5 = ((1978 ^ (n - m) : ℕ) % 125) % 5 := by
            norm_num [Nat.pow_mod, Nat.mod_mod]
          rw [h₁₆, h₁₅]
          <;> norm_num
        rw [h₁₄]
        <;> norm_num
      exact h₁₃
    have h₁₂ : (3 : ℕ) ^ (n - m) % 5 = 1 := by
      have h₁₃ : (1978 : ℕ) % 5 = 3 := by norm_num
      have h₁₄ : (1978 ^ (n - m) : ℕ) % 5 = ((1978 : ℕ) % 5) ^ (n - m) % 5 := by
        simp [Nat.pow_mod]
      rw [h₁₄, h₁₃] at h₁₁
      norm_num at h₁₁ ⊢
      <;>
      (try omega) <;>
      (try simp_all [Nat.pow_mod, Nat.mul_mod, Nat.add_mod]) <;>
      (try omega) <;>
      (try ring_nf at * <;> omega)
    have h₁₃ : (n - m) % 4 = 0 := by
      have h₁₄ : ∀ k : ℕ, (3 : ℕ) ^ k % 5 = 1 → k % 4 = 0 := by
        intro k hk
        have h₁₅ : (3 : ℕ) ^ (k % 4) % 5 = 1 := by
          rw [← Nat.mod_add_div k 4]
          simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at hk ⊢
          norm_num at *
          clear * - k hk
          apply lemma_5 <;> assumption
        have h₁₆ : k % 4 = 0 := by
          have : (3 : ℕ) ^ (k % 4) % 5 = 1 := h₁₅
          have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
          rcases this with (h | h | h | h) <;> simp [h, pow_succ, Nat.mul_mod, Nat.pow_mod] at h₁₅ ⊢ <;> omega
        exact h₁₆
      exact h₁₄ (n - m) h₁₂
    exact h₁₃
  
  have h₂ : 3 ^ (n - m) % 25 = 1 := by
    have h₂₁ : (1978 ^ (n - m) : ℕ) % 25 = 1 := by
      have h₂₂ : (1978 ^ (n - m) : ℕ) % 125 = 1 := by simpa using h₆
      have h₂₃ : (1978 ^ (n - m) : ℕ) % 25 = 1 := by
        have h₂₄ : (1978 ^ (n - m) : ℕ) % 25 = ((1978 ^ (n - m) : ℕ) % 125) % 25 := by
          norm_num [Nat.pow_mod, Nat.mod_mod]
        rw [h₂₄, h₂₂]
        <;> norm_num
      exact h₂₃
    have h₂₂ : (3 : ℕ) ^ (n - m) % 25 = 1 := by
      have h₂₃ : (1978 : ℕ) % 25 = 3 := by norm_num
      have h₂₄ : (1978 ^ (n - m) : ℕ) % 25 = ((1978 : ℕ) % 25) ^ (n - m) % 25 := by
        simp [Nat.pow_mod]
      rw [h₂₄, h₂₃] at h₂₁
      norm_num at h₂₁ ⊢
      <;>
      (try omega) <;>
      (try simp_all [Nat.pow_mod, Nat.mul_mod, Nat.add_mod]) <;>
      (try omega) <;>
      (try ring_nf at * <;> omega)
    exact h₂₂
  
  exact ⟨h₁, h₂⟩

lemma lemma_3 (n m : ℕ) (hmn : m < n) (hmod : 1978 ^ n ≡ 1978 ^ m [MOD 1000]) (h₄ : n - m ≥ 1) (h₅ : 1978 ^ n % 1000 = 1978 ^ m % 1000) :
  1978 ^ (n - m) % 125 = 1 := by
  have h_gcd : Nat.gcd 1978 125 = 1 := by
    norm_num [Nat.gcd_eq_right, Nat.gcd_eq_left]
    <;> decide
  
  have h_mod125 : 1978 ^ n ≡ 1978 ^ m [MOD 125] := by
    have h1 : 1978 ^ n ≡ 1978 ^ m [MOD 1000] := hmod
    have h2 : 1978 ^ n ≡ 1978 ^ m [MOD 125] := by
      -- Use the fact that if a ≡ b mod 1000, then a ≡ b mod 125
      have h3 : 1978 ^ n % 125 = 1978 ^ m % 125 := by
        -- Use the given congruence modulo 1000 to deduce the congruence modulo 125
        have h4 : 1978 ^ n % 1000 = 1978 ^ m % 1000 := by
          simpa [Nat.ModEq] using hmod
        have h5 : 1978 ^ n % 125 = 1978 ^ m % 125 := by
          omega
        exact h5
      -- Convert the result back to the desired form
      simpa [Nat.ModEq] using h3
    exact h2
  
  have h_pow_diff : 1978 ^ (n - m) ≡ 1 [MOD 125] := by
    have h₂ : 1978 ^ n ≡ 1978 ^ m [MOD 125] := h_mod125
    have h₃ : Nat.gcd 1978 125 = 1 := h_gcd
    have h₆ : m < n := hmn
    have h₇ : n - m > 0 := by omega
    have h₈ : n = m + (n - m) := by
      have h₈₁ : m ≤ n := by omega
      have h₈₂ : n - m + m = n := by omega
      omega
    rw [h₈] at h₂
    have h₉ : 1978 ^ (m + (n - m)) ≡ 1978 ^ m [MOD 125] := h₂
    have h₁₀ : 1978 ^ (m + (n - m)) = 1978 ^ m * 1978 ^ (n - m) := by
      rw [pow_add]
    rw [h₁₀] at h₉
    have h₁₁ : 1978 ^ m * 1978 ^ (n - m) ≡ 1978 ^ m [MOD 125] := h₉
    have h₁₂ : Nat.gcd (1978 ^ m) 125 = 1 := by
      have h₁₃ : Nat.gcd 1978 125 = 1 := h_gcd
      have h₁₄ : Nat.gcd (1978 ^ m) 125 = 1 := by
        -- Prove that gcd(1978^m, 125) = 1 using the fact that gcd(1978, 125) = 1
        have := Nat.Coprime.pow_left m h₁₃
        exact this

      exact h₁₄
    have h₁₅ : 1978 ^ (n - m) ≡ 1 [MOD 125] := by
      -- Use the cancellation law for congruences
      have h₁₆ : 1978 ^ m * 1978 ^ (n - m) ≡ 1978 ^ m * 1 [MOD 125] := by
        simpa [Nat.ModEq] using h₁₁
      have h₁₇ : 1978 ^ (n - m) ≡ 1 [MOD 125] := by
        -- Cancel 1978^m from both sides
        have h₁₈ : 1978 ^ m * 1978 ^ (n - m) ≡ 1978 ^ m * 1 [MOD 125] := h₁₆
        have h₁₉ : 1978 ^ (n - m) ≡ 1 [MOD 125] := by
          -- Use the cancellation law for congruences
          have fff := @Nat.ModEq.cancel_left_div_gcd 125 _ _ (1978^m) (by decide) h₁₆
          rw [Nat.gcd_comm, h₁₂] at fff
          norm_num at fff
          exact fff

        exact h₁₉
      exact h₁₇
    exact h₁₅
  
  have h_main : 1978 ^ (n - m) % 125 = 1 := by
    rw [Nat.ModEq] at h_pow_diff
    exact h_pow_diff
  
  apply h_main

lemma lemma_1 (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hmod : 1978 ^ n ≡ 1978 ^ m [MOD 1000]) :
  3 ≤ m := by
  have h₁ : m ≠ 1 := by
    intro h
    have h₁₁ : m = 1 := h
    have h₁₂ : n ≥ 2 := by
      omega
    have h₁₃ : 1978 ^ n % 8 = 0 ∨ 1978 ^ n % 8 = 4 := by
      have h₁₄ : ∀ k : ℕ, 0 < k → (1978 ^ k % 8 = 0 ∨ 1978 ^ k % 8 = 4 ∨ 1978 ^ k % 8 = 2) := by
        intro k hk
        induction' hk with k hk IH
        · norm_num
        · cases k with
          | zero => contradiction
          | succ k =>
            cases k with
            | zero =>
              norm_num [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod] at *
            | succ k =>
              cases IH with
              | inl h =>
                norm_num [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod] at *
                <;> omega
              | inr h =>
                cases h with
                | inl h =>
                  norm_num [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod] at *
                  <;> omega
                | inr h =>
                  norm_num [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod] at *
                  <;> omega
      have h₁₅ : 0 < n := hn
      have h₁₆ : 1978 ^ n % 8 = 0 ∨ 1978 ^ n % 8 = 4 ∨ 1978 ^ n % 8 = 2 := h₁₄ n h₁₅
      have h₁₇ : n ≥ 2 := h₁₂
      have h₁₈ : 1978 ^ n % 8 = 0 ∨ 1978 ^ n % 8 = 4 := by
        have h₁₉ : n ≥ 3 → 1978 ^ n % 8 = 0 := by
          intro hn3
          have h₂₀ : ∀ k : ℕ, k ≥ 3 → 1978 ^ k % 8 = 0 := by
            intro k hk
            induction' hk with k hk IH
            · norm_num
            · cases k with
              | zero => contradiction
              | succ k =>
                cases k with
                | zero => contradiction
                | succ k =>
                  cases k with
                  | zero => contradiction
                  | succ k =>
                    simp [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod] at *
                    <;> omega
          exact h₂₀ n hn3
        cases' lt_or_le n 3 with hn3 hn3
        · -- Case: n < 3
          have hn4 : n = 2 := by omega
          rw [hn4]
          norm_num [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod]
        · -- Case: n ≥ 3
          have hn4 : n ≥ 3 := by omega
          have hn5 : 1978 ^ n % 8 = 0 := h₁₉ hn4
          exact Or.inl hn5
      cases' h₁₈ with h₁₈ h₁₈
      · exact Or.inl h₁₈
      · exact Or.inr h₁₈
    have h₁₉ : 1978 ^ m % 8 = 2 := by
      rw [h₁₁]
      norm_num [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod]
    have h₂₀ : 1978 ^ n % 8 = 1978 ^ m % 8 := by
      have h₂₁ : 1978 ^ n % 1000 = 1978 ^ m % 1000 := by
        rw [Nat.ModEq] at hmod
        exact hmod
      have h₂₂ : 1978 ^ n % 8 = 1978 ^ m % 8 := by
        have h₂₃ : 1978 ^ n % 8 = (1978 ^ n % 1000) % 8 := by
          have h₂₄ : 1978 ^ n % 1000 % 8 = 1978 ^ n % 8 := by
            omega
          omega
        have h₂₅ : 1978 ^ m % 8 = (1978 ^ m % 1000) % 8 := by
          have h₂₆ : 1978 ^ m % 1000 % 8 = 1978 ^ m % 8 := by
            omega
          omega
        rw [h₂₃, h₂₅, h₂₁]
        <;> omega
      exact h₂₂
    have h₂₁ : 1978 ^ n % 8 = 0 ∨ 1978 ^ n % 8 = 4 := h₁₃
    cases h₂₁ with
    | inl h₂₁ =>
      omega
    | inr h₂₁ =>
      omega
  
  have h₂ : m ≠ 2 := by
    intro h
    have h₂₁ : m = 2 := h
    have h₂₂ : n ≥ 3 := by
      omega
    have h₂₃ : 1978 ^ n % 8 = 0 := by
      have h₂₄ : ∀ k : ℕ, k ≥ 3 → 1978 ^ k % 8 = 0 := by
        intro k hk
        induction' hk with k hk IH
        · norm_num
        · cases k with
          | zero => contradiction
          | succ k =>
            cases k with
            | zero => contradiction
            | succ k =>
              cases k with
              | zero => contradiction
              | succ k =>
                simp [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod] at *
                <;> omega
      exact h₂₄ n h₂₂
    have h₂₄ : 1978 ^ m % 8 = 4 := by
      rw [h₂₁]
      norm_num [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero, Nat.mod_mod]
    have h₂₅ : 1978 ^ n % 8 = 1978 ^ m % 8 := by
      have h₂₅₁ : 1978 ^ n % 1000 = 1978 ^ m % 1000 := by
        rw [Nat.ModEq] at hmod
        exact hmod
      have h₂₅₂ : 1978 ^ n % 8 = (1978 ^ n % 1000) % 8 := by
        omega
      have h₂₅₃ : 1978 ^ m % 8 = (1978 ^ m % 1000) % 8 := by
        omega
      have h₂₅₄ : (1978 ^ n % 1000) % 8 = (1978 ^ m % 1000) % 8 := by
        omega
      omega
    omega
  
  have h₃ : 3 ≤ m := by
    by_contra h₄
    -- We will show that if m < 3, then m must be either 1 or 2, which we have already ruled out.
    have h₅ : m ≤ 2 := by omega
    have h₆ : m = 1 ∨ m = 2 := by
      omega
    cases h₆ with
    | inl h₆ =>
      -- If m = 1, we have a contradiction with h₁.
      exfalso
      apply h₁
      exact h₆
    | inr h₆ =>
      -- If m = 2, we have a contradiction with h₂.
      exfalso
      apply h₂
      exact h₆
  
  exact h₃

lemma lemma_2 (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) (hmod : 1978 ^ n ≡ 1978 ^ m [MOD 1000]) :
  100 ≤ n - m := by
  have h₁ : m ≥ 3 := by
    by_contra h
    -- Assume m < 3, i.e., m = 1 or m = 2
    have h₂ : m ≤ 2 := by linarith
    have h₃ : m = 1 ∨ m = 2 := by
      omega
    -- Consider the cases m = 1 and m = 2
    have h₄ : 1978 ^ n % 8 = 1978 ^ m % 8 := by
      have h₅ : 1978 ^ n % 1000 = 1978 ^ m % 1000 := by
        simpa [Nat.ModEq] using hmod
      have h₆ : 1978 ^ n % 8 = 1978 ^ m % 8 := by
        have h₇ : 1978 ^ n % 8 = (1978 ^ n % 1000) % 8 := by
          omega
        have h₈ : 1978 ^ m % 8 = (1978 ^ m % 1000) % 8 := by
          omega
        rw [h₇, h₈, h₅]
      exact h₆
    -- Case m = 1
    have h₅ : m = 1 ∨ m = 2 := h₃
    cases h₅ with
    | inl h₅ =>
      have h₆ : m = 1 := h₅
      have h₇ : 1978 ^ m % 8 = 2 := by
        rw [h₆]
        norm_num
      have h₈ : 1978 ^ n % 8 = 2 := by
        rw [h₄, h₇]
      have h₉ : n ≥ 2 := by
        omega
      have h₁₀ : 1978 ^ n % 8 = 0 := by
        have h₁₁ : n ≥ 3 := by
          by_contra h₁₁
          have h₁₂ : n ≤ 2 := by omega
          have h₁₃ : n = 1 ∨ n = 2 := by omega
          cases h₁₃ with
          | inl h₁₃ =>
            have h₁₄ : n = 1 := h₁₃
            have h₁₅ : 1978 ^ n % 8 = 2 := by
              rw [h₁₄]
              norm_num
            omega
          | inr h₁₃ =>
            have h₁₄ : n = 2 := h₁₃
            have h₁₅ : 1978 ^ n % 8 = 4 := by
              rw [h₁₄]
              norm_num
            omega
        have h₁₆ : 1978 ^ n % 8 = 0 := by
          have h₁₇ : n ≥ 3 := h₁₁
          have h₁₈ : ∀ k : ℕ, k ≥ 3 → 1978 ^ k % 8 = 0 := by
            intro k hk
            induction' hk with k hk IH
            · norm_num
            · simp [pow_succ, Nat.mul_mod, IH, Nat.pow_mod]
              <;> norm_num <;> omega
          exact h₁₈ n h₁₇
        exact h₁₆
      omega
    | inr h₅ =>
      have h₆ : m = 2 := h₅
      have h₇ : 1978 ^ m % 8 = 4 := by
        rw [h₆]
        norm_num
      have h₈ : 1978 ^ n % 8 = 4 := by
        rw [h₄, h₇]
      have h₉ : n ≥ 3 := by
        omega
      have h₁₀ : 1978 ^ n % 8 = 0 := by
        have h₁₁ : ∀ k : ℕ, k ≥ 3 → 1978 ^ k % 8 = 0 := by
          intro k hk
          induction' hk with k hk IH
          · norm_num
          · simp [pow_succ, Nat.mul_mod, IH, Nat.pow_mod]
            <;> norm_num <;> omega
        exact h₁₁ n h₉
      omega
  
  have h₂ : n - m ≥ 100 := by
    have h₃ : n ≥ m + 1 := by omega
    have h₄ : n - m ≥ 1 := by omega
    have h₅ : 1978 ^ n % 1000 = 1978 ^ m % 1000 := by
      simpa [Nat.ModEq] using hmod
    have h₆ : 1978 ^ (n - m) % 125 = 1 := by
      apply lemma_3 n m <;> assumption
  
    have h₇ : n - m ≥ 100 := by
      -- from here we find the pattern of n - m
      -- we currently have 99 candidates but we can cut it down to 4
      clear * - h₆ h₄
      have sh : (n - m) % 4 = 0 ∧ 3^(n - m) % 25 = 1 := by
        apply lemma_4 <;> assumption
      have mf : (n - m) % 20 = 0 := by
        apply lemma_6 <;> assumption
      clear sh
      -- use omega to solve the problem
      by_contra! hh
      obtain nh | nh | nh | nh : n - m = 20 ∨ n - m = 40 ∨ n - m = 60 ∨ n - m = 80 := by omega
      -- we now have four values, just substitute them into h₆
      all_goals revert h₆; rw [nh]; decide

    exact h₇
  
  have h₃ : 100 ≤ n - m := by
    omega
  
  exact h₃


/-- 12. (IMO-20-1) The last three digits of the numbers $1978^{n}$ and $1978^{m}$ are equal. Find the positive integers $n$ and $m$ such that $n+m$ is minimized, where $n>m \geqslant 1$. -/
theorem number_theory_323659 : IsLeast { target | ∃ n m, n + m = target ∧ 0 < n ∧ 0 < m ∧ m < n ∧ 1978^n ≡ 1978^m [MOD 1000] } 106 := by
  refine' ⟨⟨103, 3, by decide⟩, fun a h => _⟩
  simp at h
  rcases h with ⟨n, m, rfl, hn, hm, hmn, hmod⟩
  have xe : 100 ≤ n - m := by
    apply lemma_2 n m <;> assumption
  have hh : 3 ≤ m := by
    apply lemma_1 n m <;> assumption
  omega
  