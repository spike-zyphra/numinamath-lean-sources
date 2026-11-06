import Mathlib

theorem number_theory_81102
    (a b c : ℕ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a % b = 2)
    (h₄ : b % c = 2)
    (h₅ : c % a = 4) :
    c = 4 := by
  by_cases h1 : a < b
  · -- If `a < b`, then `a % b = a`, so `a = 2`.
    have h1' : a % b = a := by
      rw [Nat.mod_eq_of_lt]
      linarith
    have ha1 : a = 2 := by
      linarith [h₃, h1']
    rw [ha1] at h₅
    have h1_sub2 : c % 2 < 2 := by
      apply Nat.mod_lt
      norm_num
    linarith [h₅, h1_sub2]
  · -- Case where b ≥ a
    by_cases h2 : b < c
    · -- If `b < c`, then `b % c = b`, so `b = 2`.
      have h2' : b % c = b := by
        rw [Nat.mod_eq_of_lt]
        linarith
      have hb1 : b = 2 := by
        linarith [h₄, h2']
      rw [hb1] at h₃
      have h1_sub2 : a % 2 < 2 := by
        apply Nat.mod_lt
        norm_num
      linarith [h₃, h1_sub2]
    · -- Case where c ≥ b
      by_cases h3 : c < a
      · -- If `c < a`, then `c % a = c`, so `c = 4`.
        have h3' : c % a = c := by
          rw [Nat.mod_eq_of_lt]
          linarith
        have hc1 : c = 4 := by
          linarith [h₅, h3']
        exact hc1
      · -- Case where a ≥ c
        have h3' : a ≥ c := by linarith
        have h4' : b ≥ a := by linarith
        have h5' : c ≥ b := by linarith
        -- From the inequalities, we now get a = b = c.
        have h6 : a = b := by linarith
        have h7 : b = c := by linarith
        -- Substituting a = b into a % b = 2 gives a % a = 2.
        -- But a % a = 0, giving 0 = 2, a contradiction.
        have h8 : a % a = 0 := by
          simp [Nat.mod_eq_zero_of_dvd]
        rw [show b = a by linarith [h6]] at h₃
        -- This leads to a contradiction.
        -- Similarly for b % c = 2 and c % a = 4.
        -- Therefore the only solution is when c = 4
        -- This is the only possible value that satisfies all constraints.
        omega
        <;> try { tauto }
        <;> try { tauto } <;> try norm_num
        <;> try { tauto } <;> try { contradiction }
        <;> try { tauto } <;> try { omega }