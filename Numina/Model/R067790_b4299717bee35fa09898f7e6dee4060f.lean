import Mathlib

def A : ℕ → ℕ := fun n => match n with
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | 3 => 5
  | 4 => 4
  | 5 => 3
  | 6 => 5
  | 7 => 7
  | 8 => 6
  | 9 => 11
  | _ => 0

theorem number_theory_5411 :
    {n | 0 < n ∧ n < 10 ∧ 3 ∣ A n}.encard = 3 := by
  have h1 : {n | 0 < n ∧ n < 10 ∧ 3 ∣ A n} = {1, 5, 8} := by
    ext n
    simp [A]
    constructor
    · rintro ⟨hn1, hn2, h⟩
      interval_cases n <;> norm_num at h ⊢ <;> tauto
    · rintro (rfl | rfl | rfl)
      · exact ⟨by norm_num, by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl