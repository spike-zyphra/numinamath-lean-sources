import Mathlib

theorem number_theory_3918 (n : ℤ) : ∃ x y, n = x^2 - y^2 ↔ n = 0 ∨ 4 ∣ n ∨ ¬(2 ∣ n) := by 
  by_cases h1 : n % 4 = 0
  · -- n is divisible by 4
    use (n / 4 + 1)
    use (n / 4 - 1)
    constructor
    · -- Assume n = x^2 - y^2. Show n = 0 ∨ 4 ∣ n ∨ ¬(2 ∣ n)
      intro h
      have h3 : 4 ∣ n := by 
        omega
      simp [h3, h1]
    · -- Assume n = 0 ∨ 4 ∣ n ∨ ¬(2 ∣ n). Show n = x^2 - y^2
      intro h
      rcases h with (h | h | h)
      · -- n = 0
        have hn : n = 0 := by
          omega
        rw [hn]
        norm_num
      · -- 4 ∣ n
        have h4 : 4 ∣ n := h
        have h5 : n % 4 = 0 := by
          omega
        have h6 : n = (n / 4) * 4 := by
          omega
        nlinarith [h6]
      · -- ¬(2 ∣ n)
        exfalso
        have h3 : n % 2 = 0 := by
          omega
        omega
  by_cases h2 : n % 2 = 1 
  · -- n is odd
    use (n + 1) / 2
    use (n - 1) / 2
    constructor
    · -- Assume n = x^2 - y^2. Show n = 0 ∨ 4 ∣ n ∨ ¬(2 ∣ n)
      intro h
      have h2 : ¬(2 ∣ n) := by 
        omega
      simp [h2, h2]
    · -- Assume n = 0 ∨ 4 ∣ n ∨ ¬(2 ∣ n). Show n = x^2 - y^2
      intro h
      rcases h with (h | h | h)
      · -- n = 0
        exfalso
        omega
      · -- 4 ∣ n
        exfalso
        omega
      · -- ¬(2 ∣ n)
        have h2' : n % 2 = 1 := by
          omega
        have h3 : n = ((n + 1) / 2) ^ 2 - ((n - 1) / 2) ^ 2 := by
          have h4 : n % 2 = 1 := h2
          have h5 : n = 2 * (n / 2) + 1 := by omega
          have h6 : (n + 1) / 2 = (n / 2) + 1 := by 
            omega
          have h7 : (n - 1) / 2 = (n / 2) := by 
            omega
          rw [h6, h7]
          have eq : ((n / 2) + 1) ^ 2 - ((n / 2) ) ^ 2 = n := by
            nlinarith [sq_nonneg (n / 2 : ℤ)]
          linarith
        linarith
  · -- n is even, but not divisible by 4
    have h2 : n % 4 = 2 := by 
      omega
    use 0
    use 0
    constructor
    · -- Assume n = x^2 - y^2. Show n = 0 ∨ 4 ∣ n ∨ ¬(2 ∣ n)
      intro h
      exfalso
      omega
    · -- Assume n = 0 ∨ 4 ∣ n ∨ ¬(2 ∣ n). Show n = x^2 - y^2
      intro h
      rcases h with (h | h | h)
      · -- n = 0
        exfalso
        omega
      · -- 4 ∣ 0
        exfalso
        omega
      · -- ¬(2 ∣ 0)
        exfalso
        omega