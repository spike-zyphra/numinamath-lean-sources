import Mathlib

theorem number_theory_185713 {N : ℕ} (hN : ∃ k, N = k * (k + 1)) :
    (∃ a b, a < 10 ∧ b < 10 ∧ IsSquare (N * 100 + 10 * a + b)) ∧
    (N > 12 → ∃! a, ∃! b, a < 10 ∧ b < 10 ∧ IsSquare (N * 100 + 10 * a + b)) := by
  rcases hN with ⟨k, rfl⟩
  constructor
  · -- Show existence of digits a, b such that k(k+1)*100 + 10a + b is a perfect square
    use 2, 5
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show IsSquare (k * (k + 1) * 100 + 10 * 2 + 5)
      have h1 : IsSquare ((k * (k + 1) * 100 + 10 * 2 + 5 : ℕ)) := by
        use 10 * k + 5
        ring_nf
      exact h1
  · -- Now prove the uniqueness part
    intro hN12
    have hk : k * (k + 1) > 12 := hN12
    have hk1 : k ≥ 4 := by
      by_contra h
      push_neg at h
      have : k ≤ 3 := by linarith
      interval_cases k <;> try { 
        omega 
      }
      <;> omega
    use 2
    constructor
    · -- Show unique b when a is 2
      use 5
      constructor
      · -- Show that 2 < 10, 5 < 10 ∧ IsSquare ...
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show IsSquare (k * (k + 1) * 100 + 10 * 2 + 5)
          have h1 : IsSquare ((k * (k + 1) * 100 + 10 * 2 + 5 : ℕ)) := by
            use 10 * k + 5
            ring_nf
          exact h1
      · -- Show that b is unique
        intro b hb
        rcases hb with ⟨hb1, hb2⟩
        have h1 : b < 10 := by
          have h2 : b < 10 := by
            omega
          linarith
        -- From Error 1, change below
        -- have h2 : IsSquare ((k * (k + 1) * 100 + 10 * 2 + b : ℕ)) := by
        --   simpa using hb2
        -- To correctly extract the IsSquare part from the conjunction hb2
        have h2' : IsSquare ((k * (k + 1) * 100 + 10 * 2 + b : ℕ)) := hb2.right
        have h5 : ∃ s, s * s = (k * (k + 1) * 100 + 20 + b : ℕ) := by
          rcases h2' with ⟨s, hs⟩
          refine' ⟨s, by linarith⟩
        rcases h5 with ⟨s, hs⟩
        have h9 : s = 10 * k + 5 := by
          have h10 : s ≤ 10 * k + 9 := by
            nlinarith [sq_nonneg (s - (10 * k + 9) : ℕ), sq_nonneg ((10 * k + 5) : ℕ)]
          have h11 : s ≥ 10 * k + 1 := by
            nlinarith [sq_nonneg (s - (10 * k + 1) : ℕ)]
          have h12 : s = 10 * k + 5 := by
            have h13 : s ≤ 10 * k + 9 := by linarith
            have h14 : s ≥ 10 * k + 1 := by linarith
            nlinarith
          linarith
        have h6 : b = 5 := by
          rw [h9] at hs
          nlinarith
        omega
    · -- Show that a is unique
      intro a' ha1
      rcases ha1 with ⟨b, hb1, hb2⟩
      have h1 : IsSquare ((k * (k + 1) * 100 + 10 * a' + b : ℕ)) := by
        simpa using hb1.right.right
      have h2 : ∃ s, s * s = (k * (k + 1) * 100 + 10 * a' + b : ℕ) := by
        rcases h1 with ⟨s, hs⟩
        refine' ⟨s, by linarith⟩
      rcases h2 with ⟨s, hs⟩
      have h3 : a' < 10 := hb1.left
      have h4 : b < 10 := hb1.right.left
      have h5 : s = 10 * k + 5 := by
        have h6 : s ≤ 10 * k + 9 := by
          nlinarith [sq_nonneg (s - (10 * k + 9) : ℕ), sq_nonneg ((10 * k + 5) : ℕ)]
        have h7 : s ≥ 10 * k + 1 := by
          nlinarith [sq_nonneg (s - (10 * k + 1) : ℕ)]
        have h8 : s = 10 * k + 5 := by
          have h9 : s ≤ 10 * k + 9 := by linarith
          have h10 : s ≥ 10 * k + 1 := by linarith
          nlinarith
        linarith
      have h6 : b = 5 := by 
        rw [h5] at hs
        -- The equation is : (10k + 5)^2 = k*(k+1)*100 + 10*a' + b
        -- Which simplifies to 100k^2 + 100k + 25 = 100k^2 + 100k + 10a' + b
        -- So 25 = 10a' + b
        have h_eq : 10 * a' + b = 25 := by 
          nlinarith
        -- have constraints from digits
        have h3 : a' < 10 := by 
          omega
        have h4 : b < 10 := by
          omega
        interval_cases b <;> try { 
          omega 
        } 
        <;> try { 
          omega 
        } <;> try { 
          interval_cases a' <;> omega 
        }
        <;> try { 
          interval_cases a' <;> omega 
        }
      have h7 : a' = 2 := by 
        rw [h6] at hs
        -- After substituting b=5, we have 25 = 10*a' + 5 
        -- So 20 = 10*a', which means a' = 2
        have h_eq : 10 * a' + 5 = 25 := by
          nlinarith
        omega
      omega