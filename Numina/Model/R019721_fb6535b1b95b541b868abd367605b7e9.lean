import Aesop
import Mathlib

open BigOperators Nat Rat Real Topology


theorem algebra_220236 {a d : ℤ} (h₀ : 0 < d) (h₁ : a + d ≠ 0) (h₂ : (a + d) * (a + 2 * d) = 3)
    (h₃ : (a + 2 * d) * (a + 4 * d) = -3) :
    IsLeast {x | ∃ n, x = ∑ i ∈ Finset.range n, (a + i * d)} (-9) := by

  have eq1 : (a + 2 * d) * (-3 * d) = 6 := by
    nlinarith
  have eq2 : d * (a + 2 * d) = -2 := by
    nlinarith
  have h3 : d ∣ 2 := by
    use -(a + 2 * d)
    linarith
  have h4 : d = 1 ∨ d = 2 := by
    have h5 : d ∣ 2 := h3
    have h6 : 0 < d := by linarith
    have h7 : d ≤ 2 := by
      exact Int.le_of_dvd (by linarith) h5
    interval_cases d <;> try tauto
  cases h4 with
  | inl h3 =>
    have h3' : d = 1 := h3
    rw [h3'] at eq2
    have h3a : a = -4 := by
      nlinarith
    exfalso
    have h1' : (a + d) * (a + 2 * d) = 3 := h₂
    rw [h3a, h3'] at h1'
    all_goals nlinarith
  | inr h3 =>
    have h3' : d = 2 := h3
    rw [h3'] at eq2
    have h3a : a = -5 := by
      nlinarith
    have ha : a = -5 := h3a
    have hd : d = 2 := h3'
    constructor
    · -- Show -9 is in the set
      use 3
      rw [ha, hd]
      norm_num [Finset.sum_range_succ]
    · -- Show it's the minimum
      intro x hx
      rcases hx with ⟨n, hn⟩
      rw [ha, hd] at hn
      have h6 : x = (n : ℤ) ^ 2 - 6 * (n : ℤ) := by
        have h7 : x = ∑ i in Finset.range n, ((-5 : ℤ) + (i : ℤ) * (2 : ℤ)) := by
          linarith [hn]
        have h8 : x = (n : ℤ) ^ 2 - 6 * (n : ℤ) := by
          rw [h7]
          have h9 : ∀ (n : ℕ), ∑ i in Finset.range n, ((-5 : ℤ) + (i : ℤ) * (2 : ℤ)) = (n : ℤ) ^ 2 - 6 * (n : ℤ) := by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              rw [Finset.sum_range_succ, ih]
              simp [add_assoc]
              all_goals
                ring_nf
          specialize h9 n
          simpa using h9
        linarith
      have h7 : x ≥ -9 := by
        have h8 : x = (n - 3 : ℤ) ^ 2 - 9 := by
          nlinarith
        have h9 : (n - 3 : ℤ) ^ 2 ≥ 0 := by
          apply sq_nonneg
        nlinarith
      linarith