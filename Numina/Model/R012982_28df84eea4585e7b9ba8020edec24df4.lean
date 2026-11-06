import Mathlib

theorem algebra_225408 :
    ∃ a : ℕ → ℕ,
      (∀ k ≥ 2, a k = (2 * a (k - 1) * a (k + 1)) / (a (k - 1) + a (k + 1))) ∧
      ¬∃ c, ∀ n, a n = c := by 
  use fun n =>
    if n = 0 then 1
    else 0
  constructor
  · -- First result
    intro k hk
    have hk2 : k ≥ 2 := by omega
    by_cases h6 : k = 2
    · -- If k=2
      rw [h6]
      simp [if_pos, if_neg]
      <;> omega
    · -- k > 2
      have hk5 : k > 2 := by omega
      simp [if_pos, if_neg, show k - 1 > 1 by omega, show k + 1 > 3 by omega]
      <;> omega
  · -- Second result
    intro h
    rcases h with ⟨c, hc⟩
    have h1 : (fun n => if n = 0 then 1 else 0) 0 = c := by
      apply hc 0
    have h2 : (fun n => if n = 0 then 1 else 0) 1 = c := by
      apply hc 1
    simp [if_pos, if_neg] at h1 h2
    omega