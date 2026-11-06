import Mathlib

theorem number_theory_7288 (f : ℕ → ℕ) (h1 : f 1 = 1) (h2 : ∀ n > 0, f (2 * n) = n * f n) :
    (f (2 ^ 2015)) % 10 = 2 := by
  have h3 : ∀ (k : ℕ), f (2 ^ k) = 2 ^ (k * (k - 1) / 2) := by
    intro k
    induction k with
    | zero =>
      simp [h1]
    | succ k ih =>
      have eq1 : f (2 ^ ((k + 1 : ℕ))) = (2 ^ k) * f (2 ^ k) := by
        specialize h2 (2 ^ k) (by
          have : 2 ^ k > 0 := by
            apply Nat.pos_pow_of_pos
            norm_num
          linarith
        )
        have h4 : 2 * (2 ^ k) = 2 ^ (k + 1 : ℕ) := by
          ring_nf
        rw [h4] at h2
        exact h2
      rw [eq1, ih]
      have eq2 : (2 ^ k) * (2 ^ (k * (k - 1) / 2)) = 2 ^ ((k + 1) * k / 2 : ℕ) := by
        have eq3 : (2 ^ k) * (2 ^ (k * (k - 1) / 2)) = 2 ^ (k + (k * (k - 1) / 2) : ℕ) := by
          ring_nf
        rw [eq3]
        cases k with
        | zero =>
          all_goals simp
        | succ k =>
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_succ, Nat.add_assoc]
          all_goals
            ring_nf
            <;> omega
      exact eq2
  have h4 : f (2 ^ 2015) = 2 ^ (2015 * 2014 / 2 : ℕ) := by
    apply h3
  rw [h4]
  have h5 : (2 ^ (2015 * 2014 / 2 : ℕ)) % 10 = 2 := by
    have h6 : 2015 * 2014 / 2 % 4 = 1 := by
      norm_num
    have h7 : ∀ (k : ℕ), (2 ^ (4 * k + 1)) % 10 = 2 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
        all_goals omega
    have h8 : ∃ k, 2015 * 2014 / 2 = 4 * k + 1 := by
      refine' ⟨(2015 * 2014 / 2 - 1) / 4, by omega⟩
    rcases h8 with ⟨k, hk⟩
    rw [hk] at *
    apply h7 k
  exact h5