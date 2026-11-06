import Mathlib

theorem number_theory_144569 (k : ℕ) :
    7 ∣ 2^k + 3^k ↔ ∃ m, k = 6 * m + 3 := by
  constructor
  · -- Assume 7 divides 2^k + 3^k, prove ∃ m, k = 6 * m + 3
    intro h
    have h1 : k % 6 = 3 := by
      have h2 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by 
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2)
      · -- k % 6 = 0
        have h2' : (2^k + 3^k : ℕ) % 7 = 2 := by
          have h3 : ∀ (m : ℕ), (2 ^ (6 * m) + 3 ^ (6 * m) : ℕ) % 7 = 2 := by
            intro m 
            induction m with 
            | zero =>
              norm_num 
            | succ m ih =>
              ring_nf at ih ⊢
              omega
          have h4 : k % 6 = 0 := h2 
          have h5 : ∃ m, k = 6 * m := by 
            refine' ⟨k / 6, by omega⟩ 
          rcases h5 with ⟨m, hm⟩ 
          rw [hm] at * 
          exact h3 m 
        omega 
      · -- k % 6 = 1 
        have h2' : (2^k + 3^k : ℕ) % 7 = 5 := by 
          have h3 : ∀ (m : ℕ), (2 ^ (6 * m + 1) + 3 ^ (6 * m + 1) : ℕ) % 7 = 5 := by 
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              ring_nf at ih ⊢ 
              omega 
          have h4 : k % 6 = 1 := h2 
          have h5 : ∃ m, k = 6 * m + 1 := by 
            refine' ⟨(k - 1) / 6, by omega⟩ 
          rcases h5 with ⟨m, hm⟩ 
          rw [hm] at * 
          exact h3 m 
        omega 
      · -- k % 6 = 2 
        have h2' : (2^k + 3^k : ℕ) % 7 = 6 := by 
          have h3 : ∀ (m : ℕ), (2 ^ (6 * m + 2) + 3 ^ (6 * m + 2) : ℕ) % 7 = 6 := by 
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              ring_nf at ih ⊢ 
              omega 
          have h4 : k % 6 = 2 := h2 
          have h5 : ∃ m, k = 6 * m + 2 := by 
            refine' ⟨(k - 2) / 6, by omega⟩ 
          rcases h5 with ⟨m, hm⟩ 
          rw [hm] at * 
          exact h3 m 
        omega 
      · -- k % 6 = 3 
        omega 
      · -- k % 6 = 4 
        have h2' : (2^k + 3^k : ℕ) % 7 = 6 := by 
          have h3 : ∀ (m : ℕ), (2 ^ (6 * m + 4) + 3 ^ (6 * m + 4) : ℕ) % 7 = 6 := by 
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              ring_nf at ih ⊢ 
              omega 
          have h4 : k % 6 = 4 := h2 
          have h5 : ∃ m, k = 6 * m + 4 := by 
            refine' ⟨(k - 4) / 6, by omega⟩ 
          rcases h5 with ⟨m, hm⟩ 
          rw [hm] at * 
          exact h3 m 
        omega 
      · -- k % 6 = 5 
        have h2' : (2^k + 3^k : ℕ) % 7 = 2 := by 
          have h3 : ∀ (m : ℕ), (2 ^ (6 * m + 5) + 3 ^ (6 * m + 5) : ℕ) % 7 = 2 := by 
            intro m 
            induction m with 
            | zero => 
              norm_num 
            | succ m ih => 
              ring_nf at ih ⊢ 
              omega 
          have h4 : k % 6 = 5 := h2 
          have h5 : ∃ m, k = 6 * m + 5 := by 
            refine' ⟨(k - 5) / 6, by omega⟩ 
          rcases h5 with ⟨m, hm⟩ 
          rw [hm] at * 
          exact h3 m 
        omega 
    have h4 : ∃ m, k = 6 * m + 3 := by 
      refine' ⟨k / 6, by omega⟩ 
    exact h4 
  · -- Assume ∃ m, k = 6 * m + 3 prove 7 ∣ 2^k + 3^k
    rintro ⟨m, hm⟩
    have h6 : ∀ (m : ℕ), 7 ∣ 2 ^ (6 * m + 3) + 3 ^ (6 * m + 3) := by
      intro m
      induction m with
      | zero =>
        norm_num
      | succ m ih =>
        norm_num [pow_succ, pow_mul, Nat.pow_add, mul_add] at ih ⊢
        all_goals omega
    have h7 : k = 6 * m + 3 := by
      omega
    rw [h7]
    exact h6 m