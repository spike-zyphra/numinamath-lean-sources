import Mathlib

/- The positive integer solutions of the equation ${{m}^{2}}-2mn+14{{n}^{2}}=217$ are $\left( m,n \right)=$ ___          ___ ， ___          ___ ， ___          ___. -/
theorem number_theory_4718 (m n : ℤ) (h : m > 0 ∧ n > 0) :
    m^2 - 2 * m * n + 14 * n^2 = 217 ↔ (m, n) = (13, 3) ∨ (m, n) = (1, 4) ∨ (m, n) = (7, 4) := by 
  constructor
  · -- Assume h1, prove the three possible values
    intro h1
    have h1' : m^2 - 2 * m * n + 14 * n^2 = 217 := h1
    have h2 : n > 0 := h.2
    have h3 : m > 0 := h.1

    have h4 : n ≤ 4 := by
      nlinarith [sq_nonneg (m - n), sq_nonneg (n), h1']

    have hn1 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by 
      omega

    rcases hn1 with hn | hn | hn | hn
    · -- n = 1
      rw [hn] at h1
      exfalso
      have h5 : m ≤ 16 := by nlinarith [h1]
      interval_cases m <;> omega
    · -- n = 2
      rw [hn] at h1
      exfalso
      have h5 : m ≤ 18 := by nlinarith [h1]
      interval_cases m <;> omega
    · -- n = 3
      rw [hn] at h1
      have h5 : m = 13 := by
        nlinarith [sq_nonneg (m - 13), sq_nonneg (n - 3)]
      left
      simp [Prod.ext_iff, h5, hn]
    · -- n = 4
      rw [hn] at h1
      have h5 : m = 1 ∨ m = 7 := by
        have h5 : m^2 - 8 * m + 7 = 0 := by
          nlinarith
        have h6 : m^2 - 8 * m + 7 = (m - 1) * (m - 7) := by ring
        rw [h6] at h5
        cases' (mul_eq_zero.mp h5) with h7 h8
        · -- Case $m - 1 = 0$
          omega
        · -- Case $m - 7 = 0$
          omega
      rcases h5 with h5' | h5'
      · -- m = 1
        right
        left
        simp [Prod.ext_iff, h5', hn]
      · -- m = 7
        right
        right
        simp [Prod.ext_iff, h5', hn]
  · -- Assume the disjunction, prove h1
    rintro (h | h | h)
    · -- (13, 3)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (1, 4)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (7, 4)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num