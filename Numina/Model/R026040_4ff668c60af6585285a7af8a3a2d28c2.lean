import Mathlib

theorem algebra_11112 (x : ℕ) : (2 : ℝ)^8 = 16^x ↔ x = 2 := by
  constructor
  · -- Assume (2 : ℝ) ^ 8 = 16 ^ x, prove x = 2
    intro h
    have h1 : (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x : ℕ) := by
      have h2 : ∀ (x : ℕ), (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x : ℕ) := by
        intro x
        induction x with
        | zero =>
          simp
        | succ x ih =>
          simp [pow_succ] at ih ⊢
          <;> ring_nf at ih ⊢
          <;> norm_num at ih ⊢
          <;> linarith
      specialize h2 x
      simpa using h2
    rw [h1] at h
    have h2 : (8 : ℕ) = 4 * x := by
      have h2 : (2 : ℝ) ^ (8 : ℕ) = (2 : ℝ) ^ (4 * x : ℕ) := by
        exact_mod_cast h
      have h3 : (8 : ℕ) = (4 * x : ℕ) := by
        exact Nat.cast_injective ((by simpa using h2 : (8 : ℕ) = (4 * x : ℕ)))
      exact h3
    have h4 : x = 2 := by
      omega
    exact h4
  · -- Assume x = 2, prove (2 : ℝ)^8 = 16^x
    rintro h
    rw [h]
    norm_num