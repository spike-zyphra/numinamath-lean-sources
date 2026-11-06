import Mathlib

/- The number of toy cars that Ray has is a multiple of $6$. When he loses two of them, the number of cars that he has left is a multiple of $n$. If $n$ is a positive even integer less than $10$, then how many possible values are there for $n$? -/
theorem number_theory_19577 :
    {n : ℕ | ∃ m, 0 < m ∧ 6 ∣ m ∧ n ∣ m - 2 ∧ Even n ∧ n < 10}.ncard = 3 := by
  have h : {n : ℕ | ∃ m, 0 < m ∧ 6 ∣ m ∧ n ∣ m - 2 ∧ Even n ∧ n < 10} = {2, 4, 8} := by
    ext n
    apply Iff.intro
    . -- Show that n is 2, 4 or 8 if it is in the set on the left.
      simp
      intro m h₀ h₁ h₂ h₃ h₄
      rw [dvd_iff_exists_eq_mul_right] at h₁ h₂
      obtain ⟨a, h₁⟩ := h₁
      obtain ⟨c, h₂⟩ := h₂
      simp [Even] at h₃
      obtain ⟨n', h₃⟩ := h₃
      rw [<-mul_two] at h₃
      rw [h₁, h₃] at h₂
      replace h₂ : (3 * a - 1) * 2 = (n' * c) * 2 := by
        rw [Nat.sub_mul, mul_comm, <-mul_assoc]
        simp
        rw [mul_assoc, mul_comm c 2, <-mul_assoc]
        exact h₂
      simp at h₂
      -- Show that 3a = n'c + 1, and we can then consider cases of n'.
      replace h₂ : 3 * a = n' * c + 1 := by
        omega
      have h₄ : n' < 5 := by
        omega
      interval_cases n'
      all_goals
        omega
    . -- Show that 2, 4, 8 is in the set on the left.
      simp
      rintro (hn₁ | hn₂ | hn₃)
      . -- When n = 2, use m = 6.
        use 6
        subst hn₁
        simp
        omega
      . -- When n = 4, use m = 6.
        use 6
        subst hn₂
        simp
        rw [even_iff_two_dvd]
        omega
      . -- When n = 8, use m = 18.
        use 18
        subst hn₃
        simp
        refine ⟨by omega, by omega, by rw [even_iff_two_dvd]; omega⟩
  rw [h]
  norm_num
