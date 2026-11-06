import Mathlib

theorem number_theory_127909 (n : ℕ) :
    Even (n * (n + 1)) ∧ 6 ∣ n * (n + 1) * (2 * n + 1) := by
  constructor
  · -- Show that $n(n+1)$ is even
    have h1 : Even (n * (n + 1)) := by
      cases (Nat.even_or_odd n) with
      | inl h =>
        have : Even (n * (n + 1)) := by
          rw [Nat.even_mul]
          simp [Nat.even_iff, h]
          all_goals omega
        exact this
      | inr h =>
        have h2 : Even (n + 1) := by
          obtain ⟨k, hk⟩ := h
          use k + 1
          rw [hk]
          all_goals omega
        have : Even (n * (n + 1)) := by
          rw [Nat.even_mul]
          simp [Nat.even_iff, h2]
          all_goals omega
        exact this
    exact h1
  · -- Show that $6$ divides $n(n+1)(2n+1)$
    have h2 : 6 ∣ n * (n + 1) * (2 * n + 1) := by
      have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      rcases h1 with (h | h | h)
      · -- Case n % 3 = 0
        have h3 : (n * (n + 1) * (2 * n + 1)) % 3 = 0 := by
          simp [Nat.mul_mod, Nat.add_mod, h]
          all_goals omega
        have h6 : (n * (n + 1) * (2 * n + 1)) % 2 = 0 := by
          have e : Even (n * (n + 1)) := by
            cases (Nat.even_or_odd n) with
            | inl h =>
              have : Even (n * (n + 1)) := by
                rw [Nat.even_mul]
                simp [Nat.even_iff, h]
                all_goals omega
              exact this
            | inr h =>
              have h2 : Even (n + 1) := by
                obtain ⟨k, hk⟩ := h
                use k + 1
                rw [hk]
                all_goals omega
              have : Even (n * (n + 1)) := by
                rw [Nat.even_mul]
                simp [Nat.even_iff, h2]
                all_goals omega
              exact this
          have e2 : (n * (n + 1)) % 2 = 0 := by
            exact Nat.even_iff.1 e
          calc (n * (n + 1) * (2 * n + 1)) % 2
            = ((n * (n + 1)) % 2) * ((2 * n + 1) % 2) % 2 := by simp [Nat.mul_mod]
            _ = (0) * ((2 * n + 1) % 2) % 2 := by rw [e2]
            _ = 0 := by simp
        have : (n * (n + 1) * (2 * n + 1)) % 6 = 0 := by
          omega
        exact Nat.dvd_of_mod_eq_zero this
      · -- Case n % 3 = 1
        have h3 : (n * (n + 1) * (2 * n + 1)) % 3 = 0 := by
          simp [Nat.mul_mod, Nat.add_mod, h]
          all_goals omega
        have h6 : (n * (n + 1) * (2 * n + 1)) % 2 = 0 := by
          have e : Even (n * (n + 1)) := by
            cases (Nat.even_or_odd n) with
            | inl h =>
              have : Even (n * (n + 1)) := by
                rw [Nat.even_mul]
                simp [Nat.even_iff, h]
                all_goals omega
              exact this
            | inr h =>
              have h2 : Even (n + 1) := by
                obtain ⟨k, hk⟩ := h
                use k + 1
                rw [hk]
                all_goals omega
              have : Even (n * (n + 1)) := by
                rw [Nat.even_mul]
                simp [Nat.even_iff, h2]
                all_goals omega
              exact this
          have e2 : (n * (n + 1)) % 2 = 0 := by
            exact Nat.even_iff.1 e
          calc (n * (n + 1) * (2 * n + 1)) % 2
            = ((n * (n + 1)) % 2) * ((2 * n + 1) % 2) % 2 := by simp [Nat.mul_mod]
            _ = (0) * ((2 * n + 1) % 2) % 2 := by rw [e2]
            _ = 0 := by simp
        have : (n * (n + 1) * (2 * n + 1)) % 6 = 0 := by
          omega
        exact Nat.dvd_of_mod_eq_zero this
      · -- Case n % 3 = 2
        have h3 : (n * (n + 1) * (2 * n + 1)) % 3 = 0 := by
          simp [Nat.mul_mod, Nat.add_mod, h]
          all_goals omega
        have h6 : (n * (n + 1) * (2 * n + 1)) % 2 = 0 := by
          have e : Even (n * (n + 1)) := by
            cases (Nat.even_or_odd n) with
            | inl h =>
              have : Even (n * (n + 1)) := by
                rw [Nat.even_mul]
                simp [Nat.even_iff, h]
                all_goals omega
              exact this
            | inr h =>
              have h2 : Even (n + 1) := by
                obtain ⟨k, hk⟩ := h
                use k + 1
                rw [hk]
                all_goals omega
              have : Even (n * (n + 1)) := by
                rw [Nat.even_mul]
                simp [Nat.even_iff, h2]
                all_goals omega
              exact this
          have e2 : (n * (n + 1)) % 2 = 0 := by
            exact Nat.even_iff.1 e
          calc (n * (n + 1) * (2 * n + 1)) % 2
            = ((n * (n + 1)) % 2) * ((2 * n + 1) % 2) % 2 := by simp [Nat.mul_mod]
            _ = (0) * ((2 * n + 1) % 2) % 2 := by rw [e2]
            _ = 0 := by simp
        have : (n * (n + 1) * (2 * n + 1)) % 6 = 0 := by
          omega
        exact Nat.dvd_of_mod_eq_zero this
    exact h2