import Mathlib

theorem algebra_53349 (a : ℕ → ℤ) (ha : ∀ n, a (n + 1) = a n + 7) (ha0 : a 0 = 5) :
    IsLeast {x | ∃ n, x = a n ∧ x > 2017} 2021 := by
  have h1 : ∀ n : ℕ, a n = 5 + 7 * (n : ℤ) := by 
    intro n
    induction n with
    | zero =>
      simp [ha0]
    | succ n ih =>
      have eq1 : a (n + 1) = a n + 7 := ha n
      rw [eq1]
      rw [ih]
      all_goals simp [add_mul, mul_add]
      <;> ring
  constructor 
  · -- Show 2021 is in the set.
    use 288 
    have h288 : a 288 = 2021 := by
      rw [h1 288]
      norm_num 
    constructor 
    · -- Show that 2021 = a 288
      linarith [h288] 
    · -- Show that 2021 > 2017
      norm_num 
  · -- Show that 2021 is minimal.
    intro x hx
    rcases hx with ⟨n, hn1, hn2⟩
    have h2 : a n = 5 + 7 * (n : ℤ) := h1 n
    rw [h2] at hn1
    omega