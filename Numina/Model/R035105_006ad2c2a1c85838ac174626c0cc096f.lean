import Mathlib

theorem number_theory_230235 :
    {(a, b) : ℕ × ℕ | Odd a ∧ Odd b ∧ b = a + 2 ∧ ∃ n : ℕ, a^2 + b^2 = n * (n + 1) / 2} = 
    {(1, 3)} := by
  ext ⟨a, b⟩
  simp [-one_div]
  constructor
  · -- First direction: if (a, b) in the set, then (a, b) = (1, 3)
    rintro ⟨ha, hb, h_eq, ⟨n, hn⟩⟩
    have h1 : b = a + 2 := by
      linarith 
    rw [show b = a + 2 by linarith [h1]] at hn
    have eq1 : 4 * a ^ 2 + 8 * a + 8 = n * (n + 1) := by
      have h_eq2 : a ^ 2 + (a + 2) ^ 2 = n * (n + 1) / 2 := by
        linarith
      have h_eq3 : a ^ 2 + (a + 2) ^ 2 = 2 * a ^ 2 + 4 * a + 4 := by
        ring_nf
      have h_eq4 : 2 * a ^ 2 + 4 * a + 4 = n * (n + 1) / 2 := by
        linarith [h_eq2, h_eq3]
      have eq1 : (2 * a ^ 2 + 4 * a + 4) * 2 = n * (n + 1) := by
        have h1 : n * (n + 1) % 2 = 0 := by
          have h1 : n * (n + 1) % 2 = 0 := by
            have h10 : n % 2 = 0 ∨ n % 2 = 1 := by omega
            rcases h10 with (h10 | h10)
            · -- n even
              simp [Nat.mul_mod, h10]
              all_goals omega
            · -- n odd
              have h11 : (n + 1) % 2 = 0 := by omega
              simp [Nat.mul_mod, h11]
              all_goals omega
          omega
        omega
      nlinarith
      <;> try { 
        omega 
      }
    
    -- Proving $a \leq n$
    have h3 : a ≤ n := by
      by_contra h
      push_neg at h
      have h4 : n < a := by linarith
      have h4' : n ≤ a - 1 := by omega
      have h5 : n * (n + 1) ≤ (a - 1) * a := by 
        nlinarith [sq_nonneg (n - (a - 1) : ℤ), sq_nonneg (n : ℤ), sq_nonneg ((a - 1) : ℤ)]
      nlinarith
    -- Upper bound on n
    have h4 : n ≤ 2 * a + 2 := by
      nlinarith [sq_nonneg (n - (2 * a + 2) : ℤ), sq_nonneg ((a : ℕ) : ℤ), sq_nonneg ((n : ℕ) : ℤ)]
    
    have eq2 : a = 1 := by
      -- From h3: a ≤ n and h4: n ≤ 2*a+2
      by_cases h6 : a > 1
      · -- Assume a > 1 
        have h12 : a ≥ 2 := by linarith 
        -- Since a ≥ 2, n ≥ 2
        have h13 : n ≥ a := by nlinarith
        have h14 : n ≤ 2 * a + 2 := h4
        by_cases h6' : n > 2 * a
        · -- Case n > 2*a
          have h20 : n = 2 * a + 1 ∨ n = 2 * a + 2 := by 
            omega 
          rcases h20 with (h20 | h20)
          · -- Case n = 2*a+1
            rw [show n = 2 * a + 1 by linarith [h20]] at eq1
            nlinarith 
          · -- Case n = 2*a+2
            rw [show n = 2 * a + 2 by linarith [h20]] at eq1
            nlinarith 
        · -- Case n ≤ 2*a
          have h7 : n ≤ 2 * a := by linarith 
          have h8 : n ≥ a := by nlinarith 
          have h6 : n = a ∨ n = a + 1 ∨ n = a + 2 ∨ n = a + 3 ∨ n = a + 4 ∨ n = a + 5 ∨ n ≤ 2 * a := by 
            omega 
          rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6)
          · -- Case n = a
            rw [show n = a by linarith [h6]] at eq1
            nlinarith 
          · -- Case n = a + 1
            rw [show n = a + 1 by linarith [h6]] at eq1
            nlinarith 
          · -- Case n = a + 2
            rw [show n = a + 2 by linarith [h6]] at eq1
            nlinarith 
          · -- Case n = a + 3
            rw [show n = a + 3 by linarith [h6]] at eq1
            nlinarith 
          · -- Case n = a + 4
            rw [show n = a + 4 by linarith [h6]] at eq1
            nlinarith 
          · -- Case n = a + 5
            rw [show n = a + 5 by linarith [h6]] at eq1
            nlinarith 
          · -- Case n ≤ 2*a (remaining)
            nlinarith [sq_nonneg (n - 2 : ℤ), sq_nonneg (a - 2 : ℤ), sq_nonneg (n - a : ℤ), sq_nonneg (n : ℤ), sq_nonneg (a : ℤ)]
      · -- Assume a ≤ 1
        have : a = 0 ∨ a = 1 := by
          omega
        rcases this with (h' | h')
        · -- a = 0
          have ha0 : a = 0 := by linarith [h']
          have hb0 : b = 2 := by linarith [ha0, h1]
          have h6 : Odd b := hb
          rw [hb0] at h6
          rcases h6 with ⟨m, hm⟩
          omega 
        · -- a = 1
          omega
    have eq3 : b = 3 := by
      rw [h1]
      omega 
    simp [eq2, eq3] at *
    all_goals tauto 
  · -- Second direction: (a, b) = (1, 3) implies (a, b) in the set
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Show 1 is odd
      decide
    constructor
    · -- Show 3 is odd
      decide
    constructor
    · -- Show b = a + 2
      norm_num
    · -- Show exists n, such that 1^2 + 3^2 = n * (n + 1) / 2
      use 4
      all_goals norm_num