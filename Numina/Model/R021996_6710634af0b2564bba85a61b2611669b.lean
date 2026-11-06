import Mathlib

theorem number_theory_6510 (p a : ℕ) (hp : Nat.Prime p) (hpa : a ≠ 0)
    (h : p * a = 3 * (a + 1)) : p * (a + 1) = 6 * (a + 2) := by
  have h1 : p * a = 3 * a + 3 := by
    linarith [h]

  have h4 : p > 3 := by
    by_contra h4
    push_neg at h4
    have h5 : p = 2 ∨ p = 3 := by
      interval_cases p <;> norm_num at hp ⊢ <;> tauto
    rcases h5 with (h5 | h5)
    · -- Case p = 2
      rw [h5] at h1
      omega
    · -- Case p = 3
      rw [h5] at h1
      omega

  -- We know p > 3
  -- From h1: p * a = 3 * a + 3
  -- This is a * (p - 3) = 3
  -- Therefore $a$ divides 3
  -- With $a \neq 0$, $a$ is either 1 or 3

  have h6 : a ∣ 3 := by
    have h8 : a ∣ 3 := by
      have h_eq : p * a = 3 * a + 3 := h1
      have h10 : a ∣ p * a := by
        use p
        all_goals ring
      have h11 : a ∣ 3 * a := by
        use 3
        all_goals ring
      have h12 : a ∣ (p * a - (3 * a)) := by
        apply Nat.dvd_sub'
        · exact h10
        · exact h11
      have h13 : p * a - (3 * a) = 3 := by
        omega
      have h14 : a ∣ 3 := by
        have h15 : p * a - (3 * a) = 3 := h13
        have h16 : a ∣ p * a - (3 * a) := h12
        rw [h15] at h16
        exact h16
      exact h14
    exact h8

  have h8 : a = 1 ∨ a = 3 := by
    have h9 : a ∣ 3 := h6
    have h10 : a ≤ 3 := by
      exact Nat.le_of_dvd (by linarith) h9
    interval_cases a <;> norm_num at h9 hpa ⊢
    all_goals norm_num at h9 hpa ⊢
    <;> tauto

  rcases h8 with (h8 | h8)
  · -- Case a = 1
    have h9 : a = 1 := h8
    rw [h9] at h1
    have h10 : p = 6 := by
      nlinarith
    rw [h10] at hp
    norm_num at hp
  · -- Case a = 3
    have h9 : a = 3 := h8
    rw [h9] at h1
    have h10 : p = 4 := by
      nlinarith
    rw [h10] at hp
    norm_num at hp