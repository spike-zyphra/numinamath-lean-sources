import Mathlib

def seq : ℕ → ℕ
| 0 => 5
| n + 1 => (seq n) * 10 + 5

theorem number_theory_237412 :
    IsLeast {x | ∃ n, x = seq n ∧ 495 ∣ x} 555555555555555555 := by
  constructor
  · -- Show that 555555555555555555 is in the set.
    use 17
    norm_num [seq]
  · -- Show that 555555555555555555 is the least element in the set.
    intro u hu
    rcases hu with ⟨n, rfl, h⟩
    by_contra h2
    push_neg at h2
    have h2' : n < 17 := by
      by_contra h3
      push_neg at h3
      have h3 : n ≥ 17 := by omega
      have h4 : seq n ≥ 555555555555555555 := by
        have h5 : ∀ (m : ℕ), seq (m + 17) ≥ 555555555555555555 := by
          intro m
          induction m with
          | zero =>
            norm_num [seq]
          | succ m ih =>
            simp [seq] at ih ⊢
            all_goals omega
        specialize h5 (n - 17)
        have h6 : (n - 17) + 17 = n := by
          omega
        rw [h6] at h5
        linarith
      linarith
    interval_cases n <;> norm_num [seq] at h ⊢