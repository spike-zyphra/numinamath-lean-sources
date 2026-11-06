import Mathlib

set_option maxHeartbeats 999999999999

theorem number_theory_213992 :
    {(n, m) : ℕ × ℕ | (2020 : ℚ) / 2021 = n / (n + 1) * m / (m + 1)}.ncard = 48 := by
have jaja (m n : ℕ) : (2020 / 2021 : ℚ) = n / (n + 1) * m / (m + 1) ↔ (2020 < m ∧ (m - 2020) ∣ 2020 * 2021 ∧ n = 2020 + (2020 * 2021) / (m - 2020)) := by
  have my_favorite_theorem (m n : ℕ) : (2020 / 2021 : ℚ) = n / (n + 1) * m / (m + 1) -> 2020 < m := by
    intro h
    have h1 : (2020 : ℚ) / 2021 = (n : ℚ) / (n + 1) * (m : ℚ) / (m + 1) := by 
      exact_mod_cast h
    have h2 : (2020 : ℚ) * (n + 1) * (m + 1) = 2021 * (n : ℚ) * (m : ℚ) := by
      field_simp at h1 ⊢
      nlinarith
    have h3 : 2020 * (n + 1) * (m + 1) = 2021 * n * m := by
      exact_mod_cast h2
    by_contra h4
    push_neg at h4
    have h5 : m ≤ 2020 := by
      omega
    have h6 : n * m ≤ 2020 * n := by
      nlinarith [h5, show m ≤ 2020 by omega]
    have h7 : n * m = 2020 * n + 2020 * m + 2020 := by 
      nlinarith
    nlinarith [h7, h6, show m ≤ 2020 by omega, show 0 ≤ m from by omega, show 0 ≤ n from by omega]
  have h_main : (2020 / 2021 : ℚ) = n / (n + 1) * m / (m + 1) ↔ (2020 < m ∧ (m - 2020) ∣ 2020 * 2021 ∧ n = 2020 + (2020 * 2021) / (m - 2020)) := by
    constructor
    · -- Prove the forward direction: if the equation holds, then the conditions are satisfied.
      intro h
      have h₁ : (2020 : ℚ) / 2021 = (n : ℚ) / (n + 1 : ℚ) * (m : ℚ) / (m + 1 : ℚ) := by exact_mod_cast h
      have h₂ : (n : ℚ) / (n + 1 : ℚ) * (m : ℚ) / (m + 1 : ℚ) = (n * m : ℚ) / ((n + 1 : ℚ) * (m + 1 : ℚ)) := by
        field_simp [add_comm]
        <;> ring_nf
        <;> field_simp [add_comm]
        <;> ring_nf
      rw [h₂] at h₁
      have h₃ : (2020 : ℚ) / 2021 = (n * m : ℚ) / ((n + 1 : ℚ) * (m + 1 : ℚ)) := by rw [h₁]
      have h₄ : (2020 : ℚ) * ((n + 1 : ℚ) * (m + 1 : ℚ)) = 2021 * (n * m : ℚ) := by
        have h₄₁ : ((n + 1 : ℚ) * (m + 1 : ℚ)) ≠ 0 := by
          by_contra h₄₁
          rw [h₄₁] at h₃
          norm_num at h₃ ⊢
          <;>
          (try norm_num at h₃) <;>
          (try linarith) <;>
          (try ring_nf at h₃ ⊢) <;>
          (try field_simp at h₃ ⊢) <;>
          (try norm_cast at h₃ ⊢) <;>
          (try ring_nf at h₃ ⊢) <;>
          (try nlinarith)
        field_simp at h₃
        nlinarith
      have h₅ : 2020 * ((n + 1) * (m + 1) : ℕ) = 2021 * (n * m : ℕ) := by
        norm_cast at h₄ ⊢
        <;>
        ring_nf at h₄ ⊢ <;>
        norm_num at h₄ ⊢ <;>
        nlinarith
      have h₆ : n > 2020 := by
        have aj := my_favorite_theorem n m (by rw [h]; ring)
        clear * - aj
        linarith
      have h₇ : m > 2020 := by
        have aj := my_favorite_theorem m n h
        clear * - aj
        linarith
      have h₈ : (n - 2020) * (m - 2020) = 2020 * 2021 := by
        have h₈₁ : n ≥ 2021 := by omega
        have h₈₂ : m ≥ 2021 := by omega
        have h₈₃ : 2020 * ((n + 1) * (m + 1) : ℕ) = 2021 * (n * m : ℕ) := by
          exact h₅
        have h₈₄ : (n - 2020) * (m - 2020) = 2020 * 2021 := by
          qify [h₆, h₇]
          ring_nf at h₄
          ring_nf
          linarith

        exact h₈₄
      have h₉ : (m - 2020) ∣ 2020 * 2021 := by
        have h₉₁ : (n - 2020) * (m - 2020) = 2020 * 2021 := h₈
        have h₉₂ : (m - 2020) ∣ 2020 * 2021 := by
          use (n - 2020)
          <;>
          linarith
        exact h₉₂
      have h₁₀ : n = 2020 + (2020 * 2021) / (m - 2020) := by
        have h₁₀₁ : (n - 2020) * (m - 2020) = 2020 * 2021 := h₈
        have h₁₀₂ : m > 2020 := h₇
        have h₁₀₃ : (m - 2020) ∣ 2020 * 2021 := h₉
        have h₁₀₄ : n = 2020 + (2020 * 2021) / (m - 2020) := by
          have h₁₀₅ : n ≥ 2021 := by omega
          have h₁₀₆ : m ≥ 2021 := by omega
          have h₁₀₇ : (n - 2020) = (2020 * 2021) / (m - 2020) := by
            have h₁₀₈ : (m - 2020) ∣ 2020 * 2021 := h₉
            have h₁₀₉ : (n - 2020) * (m - 2020) = 2020 * 2021 := h₈
            have h₁₁₀ : (n - 2020) = (2020 * 2021) / (m - 2020) := by
              rw [← h₁₀₉]
              rw [Nat.mul_div_cancel]
              clear * - h₁₀₂
              omega
            exact h₁₁₀
          have h₁₁₁ : n = 2020 + (2020 * 2021) / (m - 2020) := by
            have h₁₁₂ : n ≥ 2021 := by omega
            have h₁₁₃ : m ≥ 2021 := by omega
            have h₁₁₄ : (n - 2020) = (2020 * 2021) / (m - 2020) := h₁₀₇
            have h₁₁₅ : n = 2020 + (2020 * 2021) / (m - 2020) := by
              have h₁₁₆ : n = 2020 + (n - 2020) := by
                omega
              rw [h₁₁₆]
              <;> omega
            exact h₁₁₅
          exact h₁₁₁
        exact h₁₀₄
      exact ⟨by omega, h₉, h₁₀⟩
    · -- Prove the reverse direction: if the conditions are satisfied, then the equation holds.
      rintro ⟨h₁, h₂, h₃⟩
      have h₄ : m > 2020 := by omega
      have h₅ : (m - 2020) ∣ 2020 * 2021 := h₂
      have h₆ : n = 2020 + (2020 * 2021) / (m - 2020) := h₃
      have h₇ : (n - 2020) * (m - 2020) = 2020 * 2021 := by
        have h₇₁ : n ≥ 2021 := by
          have h₇₂ : n = 2020 + (2020 * 2021) / (m - 2020) := h₆
          have h₇₃ : (m - 2020) ∣ 2020 * 2021 := h₂
          have h₇₄ : m > 2020 := h₄
          have h₇₅ : (2020 * 2021) / (m - 2020) ≥ 1 := by
            have h₇₆ : (m - 2020) ∣ 2020 * 2021 := h₂
            have h₇₇ : (m - 2020) ≤ 2020 * 2021 := Nat.le_of_dvd (by norm_num) h₇₆
            have h₇₈ : (2020 * 2021) / (m - 2020) ≥ 1 := by
              apply Nat.one_le_div_iff (by omega) |>.mpr
              have h₇₉ : m - 2020 ≤ 2020 * 2021 := Nat.le_of_dvd (by norm_num) h₇₆
              nlinarith
            exact h₇₈
          omega
        have h₇₂ : m ≥ 2021 := by omega
        have h₇₃ : (n - 2020) * (m - 2020) = 2020 * 2021 := by
          have h₇₄ : n = 2020 + (2020 * 2021) / (m - 2020) := h₆
          have h₇₅ : (m - 2020) ∣ 2020 * 2021 := h₂
          have h₇₆ : (n - 2020) = (2020 * 2021) / (m - 2020) := by
            have h₇₇ : n = 2020 + (2020 * 2021) / (m - 2020) := h₆
            have h₇₈ : n ≥ 2021 := by omega
            have h₇₉ : (2020 * 2021) / (m - 2020) ≥ 1 := by
              have h₇₁₀ : (m - 2020) ∣ 2020 * 2021 := h₂
              have h₇₁₁ : (m - 2020) ≤ 2020 * 2021 := Nat.le_of_dvd (by norm_num) h₇₁₀
              have h₇₁₂ : (2020 * 2021) / (m - 2020) ≥ 1 := by
                apply Nat.one_le_div_iff (by omega) |>.mpr
                have h₇₁₃ : m - 2020 ≤ 2020 * 2021 := Nat.le_of_dvd (by norm_num) h₇₁₀
                nlinarith
              exact h₇₁₂
            omega
          have h₇₈ : (n - 2020) * (m - 2020) = 2020 * 2021 := by
            have h₇₉ : (n - 2020) = (2020 * 2021) / (m - 2020) := h₇₆
            rw [h₇₉]
            have h₈₀ : (m - 2020) ∣ 2020 * 2021 := h₂
            have h₈₁ : (2020 * 2021) / (m - 2020) * (m - 2020) = 2020 * 2021 := by
              apply Nat.div_mul_cancel h₈₀
            nlinarith
          exact h₇₈
        exact h₇₃
      have h₈ : 2020 * ((n + 1) * (m + 1) : ℕ) = 2021 * (n * m : ℕ) := by
        have h₈₁ : n ≥ 2021 := by
          have h₈₂ : n = 2020 + (2020 * 2021) / (m - 2020) := h₆
          have h₈₃ : (m - 2020) ∣ 2020 * 2021 := h₂
          have h₈₄ : m > 2020 := h₄
          have h₈₅ : (2020 * 2021) / (m - 2020) ≥ 1 := by
            have h₈₆ : (m - 2020) ∣ 2020 * 2021 := h₂
            have h₈₇ : (m - 2020) ≤ 2020 * 2021 := Nat.le_of_dvd (by norm_num) h₈₆
            have h₈₈ : (2020 * 2021) / (m - 2020) ≥ 1 := by
              apply Nat.one_le_div_iff (by omega) |>.mpr
              have h₈₉ : m - 2020 ≤ 2020 * 2021 := Nat.le_of_dvd (by norm_num) h₈₆
              nlinarith
            exact h₈₈
          omega
        have h₈₂ : m ≥ 2021 := by omega
        have h₈₃ : (n - 2020) * (m - 2020) = 2020 * 2021 := h₇
        have h₈₄ : 2020 * ((n + 1) * (m + 1) : ℕ) = 2021 * (n * m : ℕ) := by
          zify [(by linarith : n ≥ 2020), (by linarith : m ≥ 2020)] at h₈₃
          zify
          ring_nf at h₈₃
          ring_nf
          linarith
        exact h₈₄
      have h₉ : (2020 : ℚ) / 2021 = (n * m : ℚ) / ((n + 1 : ℚ) * (m + 1 : ℚ)) := by
        have h₉₁ : (2020 : ℚ) * ((n + 1 : ℚ) * (m + 1 : ℚ)) = 2021 * (n * m : ℚ) := by
          qify at h₈
          assumption
        have h₉₂ : ((n + 1 : ℚ) * (m + 1 : ℚ)) ≠ 0 := by
          have midmid : (n + 1) * (m + 1) ≠ 0 := by clear * -; ring_nf; omega
          qify at midmid
          exact midmid
        field_simp at h₉₁ ⊢
        <;>
        ring_nf at h₉₁ ⊢ <;>
        assumption
      have h₁₀ : (2020 : ℚ) / 2021 = (n : ℚ) / (n + 1 : ℚ) * (m : ℚ) / (m + 1 : ℚ) := by
        have h₁₀₁ : (n : ℚ) / (n + 1 : ℚ) * (m : ℚ) / (m + 1 : ℚ) = (n * m : ℚ) / ((n + 1 : ℚ) * (m + 1 : ℚ)) := by
          field_simp [add_comm]
          <;> ring_nf
          <;> field_simp [add_comm]
          <;> ring_nf
        rw [h₁₀₁]
        exact h₉
      exact_mod_cast h₁₀
  exact h_main
simp_rw [jaja]
-- now we just need a bijection to the list of divisors 
have bij : {x : ℕ × ℕ | 2020 < x.2 ∧ x.2 - 2020 ∣ 2020 * 2021 ∧ x.1 = 2020 + 2020 * 2021 / (x.2 - 2020)}.ncard = Set.ncard (↑(Nat.divisors (2020 * 2021)) : Set ℕ) := by
  apply Set.ncard_congr (fun a ha => a.2 - 2020)
  · simp; omega
  · simp
    intro a b a_1 b_1 hb hdiv ha hb₁ hdiv₁ ha₁ hsub
    have h_b_eq_b₁ : b = b_1 := by
      have h₁ : b ≥ 2021 := by omega
      have h₂ : b_1 ≥ 2021 := by omega
      have h₃ : b = 2020 + (b - 2020) := by
        have h₄ : b - 2020 + 2020 = b := by omega
        omega
      have h₄ : b_1 = 2020 + (b_1 - 2020) := by
        have h₅ : b_1 - 2020 + 2020 = b_1 := by omega
        omega
      have h₅ : b - 2020 = b_1 - 2020 := hsub
      omega
    
    have h_a_eq_a₁ : a = a_1 := by
      rw [h_b_eq_b₁] at ha hdiv hsub
      -- Substitute b_1 for b in the equation for a
      have h₁ : a = 2020 + 4082420 / (b_1 - 2020) := by simpa [h_b_eq_b₁] using ha
      -- Use the fact that a and a_1 are defined the same way to show they are equal
      have h₂ : a_1 = 2020 + 4082420 / (b_1 - 2020) := ha₁
      linarith
    
    have h_final : a = a_1 ∧ b = b_1 := by
      refine' ⟨h_a_eq_a₁, h_b_eq_b₁⟩
    
    exact h_final
  · simp
    intro b hb
    have h_b_pos : b ≠ 0 := by
      by_contra h
      rw [h] at hb
      norm_num at hb
      <;> contradiction
    
    have h_b₁_def : ∃ (b_1 : ℕ), b_1 = b + 2020 := by
      refine' ⟨b + 2020, _⟩
      <;> rfl
    
    have h_main : ∃ a b_1, (2020 < b_1 ∧ b_1 - 2020 ∣ 4082420 ∧ a = 2020 + 4082420 / (b_1 - 2020)) ∧ b_1 - 2020 = b := by
      use 2020 + 4082420 / b, b + 2020
      have h₁ : 2020 < b + 2020 := by
        have h₂ : b ≥ 1 := by
          by_contra h₃
          -- If b is not ≥ 1, then b must be 0 because b is a natural number.
          interval_cases b <;> norm_num at hb ⊢ <;> omega
        omega
      have h₂ : (b + 2020) - 2020 ∣ 4082420 := by
        have h₃ : (b + 2020) - 2020 = b := by
          have h₄ : b ≥ 1 := by
            by_contra h₅
            interval_cases b <;> norm_num at hb ⊢ <;> omega
          omega
        rw [h₃]
        exact hb
      have h₃ : 2020 + 4082420 / b = 2020 + 4082420 / ((b + 2020) - 2020) := by
        have h₄ : (b + 2020) - 2020 = b := by
          have h₅ : b ≥ 1 := by
            by_contra h₆
            interval_cases b <;> norm_num at hb ⊢ <;> omega
          omega
        rw [h₄]
      have h₄ : (b + 2020) - 2020 = b := by
        have h₅ : b ≥ 1 := by
          by_contra h₆
          interval_cases b <;> norm_num at hb ⊢ <;> omega
        omega
      exact ⟨⟨h₁, h₂, by omega⟩, by omega⟩
    
    exact h_main
simp_rw [bij]
simp
-- Now we need to compute the cardinality of this set, which is simply the number of divisors of 2020 * 2021
native_decide
