import Mathlib

/- A sequence of numbers has 6 as its first term, and every term after the first is defined as follows: If a term, $t$, is even, the next term in the sequence is $\frac{1}{2} t$. If a term, $s$, is odd, the next term is $3 s+1$. Thus, the first four terms in the sequence are $6,3,10,5$. The 100th term is
(A) 1
(B) 2
(C) 3
(D) 4
(E) 6 -/
theorem number_theory_275985 (a : ℕ → ℕ)
    (h₀ : a 0 = 6)
    (h₁ : ∀ n, Even (a n) → a (n + 1) = a n / 2)
    (h₂ : ∀ n, Odd (a n) → a (n + 1) = 3 * a n + 1) :
    a 99 = 4 := by
  -- Write out the first few terms to spot a pattern.
  have h_a1 : a 1 = 3 := by
    have h_even_0 : Even (a 0) := by rw [h₀]; exact ⟨3, rfl⟩
    have h : a 1 = a 0 / 2 := h₁ 0 h_even_0
    rw [h₀] at h
    exact h
  have h_a2 : a 2 = 10 := by
    have h_odd_1 : Odd (a 1) := by rw [h_a1]; exact ⟨1, by norm_num⟩
    have h : a 2 = 3 * a 1 + 1 := h₂ 1 h_odd_1
    rw [h_a1] at h
    exact h
  have h_a3 : a 3 = 5 := by
    have h_even_2 : Even (a 2) := by rw [h_a2]; exact ⟨5, rfl⟩
    have h : a 3 = a 2 / 2 := h₁ 2 h_even_2
    rw [h_a2] at h
    exact h
  have h_a4 : a 4 = 16 := by
    have h_odd_3 : Odd (a 3) := by rw [h_a3]; exact ⟨2, by norm_num⟩
    have h : a 4 = 3 * a 3 + 1 := h₂ 3 h_odd_3
    rw [h_a3] at h
    exact h
  have h_a5 : a 5 = 8 := by
    have h_even_4 : Even (a 4) := by rw [h_a4]; exact ⟨8, rfl⟩
    have h : a 5 = a 4 / 2 := h₁ 4 h_even_4
    rw [h_a4] at h
    exact h
  have h_a6 : a 6 = 4 := by
    have h_even_5 : Even (a 5) := by rw [h_a5]; exact ⟨4, rfl⟩
    have h : a 6 = a 5 / 2 := h₁ 5 h_even_5
    rw [h_a5] at h
    exact h
  have h_a7 : a 7 = 2 := by
    have h_even_6 : Even (a 6) := by rw [h_a6]; exact ⟨2, rfl⟩
    have h : a 7 = a 6 / 2 := h₁ 6 h_even_6
    rw [h_a6] at h
    exact h
  have h_a8 : a 8 = 1 := by
    have h_even_7 : Even (a 7) := by rw [h_a7]; exact ⟨1, rfl⟩
    have h : a 8 = a 7 / 2 := h₁ 7 h_even_7
    rw [h_a7] at h
    exact h
  have h_a9 : a 9 = 4 := by
    have h_odd_8 : Odd (a 8) := by rw [h_a8]; exact ⟨0, by norm_num⟩
    have h : a 9 = 3 * a 8 + 1 := h₂ 8 h_odd_8
    rw [h_a8] at h
    exact h
  -- If a term repeats, the sequence will cycle.
  have h_cycle_start : a 9 = a 6 := by rw [h_a9, h_a6]
  -- The terms starting with the 7th cycle $4, 2, 1$.
  have h_cycle_1 : a (6 + 3) = a 6 := h_cycle_start
  have h_cycle_2 : a (6 + 1) = 2 := h_a7
  have h_cycle_3 : a (6 + 2) = 1 := h_a8
  -- The cycle has length $3$.
  have h_mod_0 : ∀ k, a (6 + 3 * k) = 4 := by
    intro k
    induction k with
    | zero => exact h_a6
    | succ k ih =>
      have h : a (6 + 3 * (k + 1)) = a (6 + 3 * k + 3) := by
        rw [Nat.mul_succ, Nat.add_assoc]
      have h_even_1 : Even (a (6 + 3 * k)) := by
        rw [ih]
        exact ⟨2, rfl⟩
      have h_step_1 : a (6 + 3 * k + 1) = a (6 + 3 * k) / 2 := h₁ (6 + 3 * k) h_even_1
      have h_a_6_3k_1 : a (6 + 3 * k + 1) = 2 := by omega
      have h_even_2 : Even (a (6 + 3 * k + 1)) := by
        rw [h_a_6_3k_1]
        exact ⟨1, rfl⟩
      have h_step_2 : a (6 + 3 * k + 2) = a (6 + 3 * k + 1) / 2 := h₁ (6 + 3 * k + 1) h_even_2
      have h_a_6_3k_2 : a (6 + 3 * k + 2) = 1 := by omega
      have h_odd : Odd (a (6 + 3 * k + 2)) := by
        rw [h_a_6_3k_2]
        exact ⟨0, by norm_num⟩
      have h_step : a (6 + 3 * k + 3) = 3 * a (6 + 3 * k + 2) + 1 := h₂ (6 + 3 * k + 2) h_odd
      have h_final : a (6 + 3 * k + 3) = 4 := by omega
      rw [h, h_final]
  -- Compute $a 99$, where $99 = 6 + 3 * 31$.
  have h_99 : 99 = 6 + 3 * 31 := by norm_num
  have h_a99 : a 99 = 4 := by
    rw [h_99]
    exact h_mod_0 31
  exact h_a99
