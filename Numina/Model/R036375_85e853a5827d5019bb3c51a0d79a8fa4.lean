import Mathlib

theorem number_theory_187450 (s : ℕ) :
    (∀ n : ℤ, ¬∃ x : ℤ, x^2 - 8 * n * x + 7^s = 0) ↔ Even s := by
  constructor
  · -- Assume h : ∀ n : ℤ, ¬∃ x, x ^ 2 - 8 * n * x + 7 ^ s = 0, prove s is even
    intro h
    by_contra h1
    push_neg at h1
    have h2 : s % 2 = 1 := by
      have h4 : s % 2 = 1 := by
        by_contra h5
        push_neg at h5
        have : Even s := ⟨s / 2, by omega⟩
        simp [this] at h1
        all_goals tauto
      exact h4
    have h3 : (7 ^ s : ℤ) % 8 = 7 := by
      have h8 : ∀ k : ℕ, (7 ^ (2 * k + 1 : ℕ) : ℤ) % 8 = 7 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals
            omega
      have h9 : s = 2 * ((s - 1) / 2) + 1 := by
        omega
      rw [h9]
      have h10 : ((2 * ((s - 1) / 2 : ℕ) + 1 : ℕ) : ℕ) = (2 * ((s - 1) / 2)) + 1 := by
        omega
      all_goals
        try {
          exfalso
          <;> try { tauto }
          <;> try { norm_num }
        }
        all_goals
          try {
            exfalso
            <;> try { tauto }
            <;> try { norm_num }
          }
          <;> try { 
            have h8a := h8 ((s - 1)/2)
            tauto
          }
    
    have h4 : ∃ n : ℤ, ∃ x : ℤ, x ^ 2 - 8 * n * x + 7 ^ s = 0 := by
      use (1 + (7 ^ s : ℤ)) / 8
      use 1
      have h71 : 8 * ((1 + (7 ^ s : ℤ) ) / 8 : ℤ) = (1 + (7 ^ s : ℤ) ) := by
        have h72 : (1 + (7 ^ s : ℤ) ) % 8 = 0 := by
          omega
        have h73 : 8 ∣ (1 + (7 ^ s : ℤ) ) := by
          omega
        obtain ⟨k, hk⟩ := h73
        have : (1 + (7 ^ s : ℤ) ) = 8 * k := by linarith
        have hk_eq : ((1 + (7 ^ s : ℤ) ) / 8 : ℤ) = k := by 
          omega
        have h8n : 8 * ((1 + (7 ^ s : ℤ) ) / 8 : ℤ) = (1 + (7 ^ s : ℤ) ) := by
          omega
        linarith
      nlinarith
    rcases h4 with ⟨n, x, hx⟩
    specialize h n ⟨x, hx⟩
    contradiction
  · -- Assume s is even, prove ∀ n : ℤ, ¬∃ x, x ^ 2 - 8 * n * x + 7 ^ s = 0 
    intro heven
    intro n
    intro h1
    rcases h1 with ⟨x, hx⟩
    rcases heven with ⟨k, hk⟩
    have h2 : (7 ^ s : ℤ) % 8 = 1 := by
      have h8 : ∀ k : ℕ, (7 ^ (2 * k : ℕ) : ℤ) % 8 = 1 := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals omega
      rw [show (7 ^ s : ℤ) = 7 ^ (2 * k : ℕ) by
        rw [show s = 2 * k by
          omega
        ]
        <;> all_goals norm_num
      ]
      exact h8 k
    have h3 : (x ^ 2 : ℤ) % 8 = 7 := by
      have h4 : x ^ 2 - 8 * n * x + (7 ^ s : ℤ) = 0 := hx
      have h5 : x ^ 2 = 8 * n * x - (7 ^ s : ℤ) := by linarith
      have h6 : (x ^ 2 : ℤ) % 8 = (8 * n * x - (7 ^ s : ℤ) ) % 8 := by
        rw [h5]
      have h7 : (8 * n * x - (7 ^ s : ℤ) ) % 8 = 7 := by
        have h8a : (8 * n * x : ℤ) % 8 = 0 := by
          simp [Int.mul_emod, Int.add_emod, Int.sub_emod, Int.mul_emod]
        have h8b : (7 ^ s : ℤ) % 8 = 1 := h2
        have h8c : ( (8 * n * x - (7 ^ s : ℤ) ) : ℤ ) % 8 = (0 - 1 : ℤ) % 8 := by
          simp [Int.sub_emod, h8a, h8b]
        omega
      rw [h6, h7]
    have h11 : (x ^ 2 : ℤ) % 8 = 7 := h3
    have h3_a : (x ^ 2 : ℤ) % 8 = 0 ∨ (x ^ 2 : ℤ) % 8 = 1 ∨ (x ^ 2 : ℤ) % 8 = 4 := by
      have h12 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by 
        omega
      rcases h12 with (h12 | h12 | h12 | h12 | h12 | h12 | h12 | h12) <;> 
        norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h12, Int.emod_self]
    omega