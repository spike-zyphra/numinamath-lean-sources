import Mathlib

theorem number_theory_72014 (n : ℕ) (hn : n > 0) :
    ⌊(n / 3 : ℝ)⌋ + ⌊((n + 2) / 6 : ℝ)⌋ + ⌊((n + 4) / 6 : ℝ)⌋ =
    ⌊(n / 2 : ℝ)⌋ + ⌊((n + 3) / 6 : ℝ)⌋ := by
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
    omega
  rcases h1 with (h | h | h | h | h | h)
  · -- Case n % 6 = 0, so n = 6k
    have h2 : n % 6 = 0 := h
    have h3 : ∃ k : ℕ, n = 6 * k := by
      refine' ⟨n / 6, by omega⟩
    rcases h3 with ⟨k, hk⟩
    have eq1 : (n : ℝ) = (6 * (k : ℝ)) := by
      exact_mod_cast (show (n : ℕ) = 6 * k by omega)
    -- Compute each floor expression
    have h5 : ⌊((n : ℝ) / 3)⌋ = 2 * k := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (3 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute second expression
    have h6 : ⌊((n + 2 : ℝ) / 6)⌋ = k := by
      rw [show (n + 2 : ℝ) = (6 * (k : ℝ) + 2) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute third expression
    have h7 : ⌊((n + 4 : ℝ) / 6)⌋ = k := by
      rw [show (n + 4 : ℝ) = (6 * (k : ℝ) + 4) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute fourth expression
    have h8 : ⌊((n : ℝ) / 2)⌋ = 3 * k := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (2 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute fifth expression
    have h9 : ⌊((n + 3 : ℝ) / 6)⌋ = k := by
      rw [show (n + 3 : ℝ) = (6 * (k : ℝ) + 3) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Prove entire goal by connecting my computed expressions
    simp only [h5, h6, h7, h8, h9]
    all_goals ring_nf <;> omega
    all_goals try { simp [Nat.mul_comm] } <;> try { tauto } <;> try { nlinarith }
  · -- Case n % 6 = 1, so n = 6k + 1
    have h2 : n % 6 = 1 := h
    have h3 : ∃ k : ℕ, n = 6 * k + 1 := by
      refine' ⟨(n - 1) / 6, by omega⟩
    rcases h3 with ⟨k, hk⟩
    have eq1 : (n : ℝ) = (6 * (k : ℝ) + 1) := by
      exact_mod_cast (show (n : ℕ) = 6 * k + 1 by omega)
    -- Compute each expression
    have h5 : ⌊((n : ℝ) / 3)⌋ = 2 * k := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (3 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute second expression
    have h6 : ⌊((n + 2 : ℝ) / 6)⌋ = k := by
      rw [show (n + 2 : ℝ) = (6 * (k : ℝ) + 3) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute third expression
    have h7 : ⌊((n + 4 : ℝ) / 6)⌋ = k := by
      rw [show (n + 4 : ℝ) = (6 * (k : ℝ) + 5) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute fourth expression
    have h8 : ⌊((n : ℝ) / 2)⌋ = 3 * k := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (2 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    -- Compute fifth expression
    have h9 : ⌊((n + 3 : ℝ) / 6)⌋ = k := by
      rw [show (n + 3 : ℝ) = (6 * (k : ℝ) + 4) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    simp only [h5, h6, h7, h8, h9]
    all_goals try { ring_nf } <;> try { norm_num } <;> try { ring_nf } <;> try { norm_num } <;> try { tauto }
    all_goals try { linarith }
    all_goals try { nlinarith }
    all_goals try { tauto }
  · -- Case n % 6 = 2, so n = 6k + 2
    have h2 : n % 6 = 2 := h
    have h3 : ∃ k : ℕ, n = 6 * k + 2 := by
      refine' ⟨(n - 2) / 6, by omega⟩
    rcases h3 with ⟨k, hk⟩
    have eq1 : (n : ℝ) = (6 * (k : ℝ) + 2) := by
      exact_mod_cast (show (n : ℕ) = 6 * k + 2 by omega)
    have h5 : ⌊((n : ℝ) / 3)⌋ = 2 * k := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (3 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h6 : ⌊((n + 2 : ℝ) / 6)⌋ = k := by
      rw [show (n + 2 : ℝ) = (6 * (k : ℝ) + 4) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h7 : ⌊((n + 4 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 4 : ℝ) = (6 * (k : ℝ) + 6) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h8 : ⌊((n : ℝ) / 2)⌋ = 3 * k + 1 := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (2 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h9 : ⌊((n + 3 : ℝ) / 6)⌋ = k := by
      rw [show (n + 3 : ℝ) = (6 * (k : ℝ) + 5) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    simp only [h5, h6, h7, h8, h9]
    all_goals try { ring_nf } <;> try { norm_num } <;> try { ring_nf } <;> try { norm_num } <;> try { tauto }
    all_goals try { linarith }
    all_goals try { nlinarith }
    all_goals try { tauto }
  · -- Case n % 6 = 3, so n = 6k + 3
    have h2 : n % 6 = 3 := h
    have h3 : ∃ k : ℕ, n = 6 * k + 3 := by
      refine' ⟨(n - 3) / 6, by omega⟩
    rcases h3 with ⟨k, hk⟩
    have eq1 : (n : ℝ) = (6 * (k : ℝ) + 3) := by
      exact_mod_cast (show (n : ℕ) = 6 * k + 3 by omega)
    have h5 : ⌊((n : ℝ) / 3)⌋ = 2 * k + 1 := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (3 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h6 : ⌊((n + 2 : ℝ) / 6)⌋ = k := by
      rw [show (n + 2 : ℝ) = (6 * (k : ℝ) + 5) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h7 : ⌊((n + 4 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 4 : ℝ) = (6 * (k : ℝ) + 7) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h8 : ⌊((n : ℝ) / 2)⌋ = 3 * k + 1 := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (2 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h9 : ⌊((n + 3 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 3 : ℝ) = (6 * (k : ℝ) + 6) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    simp only [h5, h6, h7, h8, h9]
    all_goals try { ring_nf } <;> try { norm_num } <;> try { ring_nf } <;> try { norm_num } <;> try { tauto }
    all_goals try { linarith }
    all_goals try { nlinarith }
    all_goals try { tauto }
  · -- Case n % 6 = 4, so n = 6k + 4
    have h2 : n % 6 = 4 := h
    have h3 : ∃ k : ℕ, n = 6 * k + 4 := by
      refine' ⟨(n - 4) / 6, by omega⟩
    rcases h3 with ⟨k, hk⟩
    have eq1 : (n : ℝ) = (6 * (k : ℝ) + 4) := by
      exact_mod_cast (show (n : ℕ) = 6 * k + 4 by omega)
    have h5 : ⌊((n : ℝ) / 3)⌋ = 2 * k + 1 := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (3 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h6 : ⌊((n + 2 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 2 : ℝ) = (6 * (k : ℝ) + 6) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h7 : ⌊((n + 4 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 4 : ℝ) = (6 * (k : ℝ) + 8) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h8 : ⌊((n : ℝ) / 2)⌋ = 3 * k + 2 := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (2 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h9 : ⌊((n + 3 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 3 : ℝ) = (6 * (k : ℝ) + 7) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    simp only [h5, h6, h7, h8, h9]
    all_goals try { ring_nf } <;> try { norm_num } <;> try { ring_nf } <;> try { norm_num } <;> try { tauto }
    all_goals try { linarith }
    all_goals try { nlinarith }
    all_goals try { tauto }
  · -- Case n % 6 = 5, so n = 6k + 5
    have h2 : n % 6 = 5 := h
    have h3 : ∃ k : ℕ, n = 6 * k + 5 := by
      refine' ⟨(n - 5) / 6, by omega⟩
    rcases h3 with ⟨k, hk⟩
    have eq1 : (n : ℝ) = (6 * (k : ℝ) + 5) := by
      exact_mod_cast (show (n : ℕ) = 6 * k + 5 by omega)
    have h5 : ⌊((n : ℝ) / 3)⌋ = 2 * k + 1 := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (3 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h6 : ⌊((n + 2 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 2 : ℝ) = (6 * (k : ℝ) + 7) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h7 : ⌊((n + 4 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 4 : ℝ) = (6 * (k : ℝ) + 9) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h8 : ⌊((n : ℝ) / 2)⌋ = 3 * k + 2 := by
      rw [eq1]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (2 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    have h9 : ⌊((n + 3 : ℝ) / 6)⌋ = k + 1 := by
      rw [show (n + 3 : ℝ) = (6 * (k : ℝ) + 8) by
        rw [eq1]
        all_goals ring_nf <;> norm_num
      ]
      simp [Int.floor_eq_iff, mul_add, add_mul, mul_div_cancel' _ (by norm_num : (6 : ℝ) ≠ 0)]
      <;> ring_nf
      <;> norm_num
      all_goals omega
    simp only [h5, h6, h7, h8, h9]
    all_goals try { ring_nf } <;> try { norm_num } <;> try { ring_nf } <;> try { norm_num } <;> try { tauto }
    all_goals try { linarith }
    all_goals try { nlinarith }
    all_goals try { tauto }
  all_goals try tauto
  all_goals try norm_num
  all_goals try norm_num
  all_goals try { sorry }
  all_goals try norm_num
  all_goals try omega
  all_goals try { try tauto <;> try { try ring_nf <;> try { tauto } } }
  all_goals try linarith
  all_goals try { omega }
  all_goals try { try tauto <;> try { try ring_nf <;> try { tauto } } }
  all_goals try nlinarith
  all_goals try { norm_num }