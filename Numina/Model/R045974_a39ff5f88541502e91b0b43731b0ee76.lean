import Mathlib

theorem number_theory_160444 (A : Set ℕ)(hA : A = {n |∃ p1 p2 p3 : ℕ, p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ n = p1 * p2 * p3 ∧ p3 = 55 * p1 * p2 + 1 ∧ p1 < p2 ∧ p2 < p3}):1986 ∈ A ∧ ∀ n ∈ A, n ≥ 1986 := by
  constructor 
  · -- Show 1986 in A
    rw [hA]
    refine ⟨2, 3, 331, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
    all_goals norm_num 
  · -- Show ∀ n ∈ A, n ≥ 1986
    intro n hn
    rw [hA] at hn
    rcases hn with ⟨p1, p2, p3, hp1, hp2, hp3, hn, hp3_eq, hp1_lt_p2, hp2_lt_p3⟩
    by_contra h
    push_neg at h
    have h1 : p1 ≥ 2 := by
      by_contra h
      push_neg at h
      have : p1 < 2 := by omega
      have : ¬p1.Prime := by 
        interval_cases p1 <;> norm_num
      contradiction
    have h2 : p2 ≥ 3 := by
      have h3 : p1 < p2 := hp1_lt_p2
      have h4 : p1 ≥ 2 := h1
      omega
    have h3k : p1 * p2 ≥ 6 := by
      have hp1 : p1 ≥ 2 := h1
      have hp2 : p2 ≥ 3 := h2
      nlinarith
    nlinarith [show p1 * p2 ≥ 6 by nlinarith, sq_nonneg (p1 * p2 - 6 : ℤ), hp3_eq, hn, Nat.Prime.two_le hp1, Nat.Prime.two_le hp2, Nat.Prime.two_le hp3]