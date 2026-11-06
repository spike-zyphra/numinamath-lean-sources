import Mathlib

theorem algebra_135652 (a : ℕ → ℤ) (ha0 : a 0 = 19) (ha1 : a 1 = 25)
    (han : ∀ n, a (n + 2) = 2 * a (n + 1) - a n) :
    IsLeast {i | 0 < i ∧ 19 ∣ a i} 19 := by
  have h1 : ∀ n, a n = 19 + 6 * (n : ℤ) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [ha0]
      <;> omega
    | succ n => 
      cases n with
      | zero => 
        simp [ha1]
        <;> omega
      | succ n => 
        have h2 := ih (n + 1) (by omega)
        have h3 := ih (n) (by omega)
        simp [han n, h2, h3]
        <;> ring_nf <;> omega
  constructor
  · -- Show that 19 belongs to the set
    constructor
    · norm_num -- 0 < (19 : ℕ)
    · -- Show that 19 divides a 19
      have h2 := h1 19
      rw [h2]
      norm_num 
      <;> omega
  · -- Show that 19 is the least element in the set
    intro i hin
    rcases hin with ⟨hi_pos, hi_div⟩
    have h2 := h1 i
    rw [h2] at hi_div
    omega
    <;> omega
    all_goals norm_num at hi_div ⊢ 
    all_goals omega