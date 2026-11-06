import Mathlib

theorem number_theory_124402 {n d : ℕ} (h₀ : 0 < n) (h₁ : d ∣ n) :
    ∃ k, k ∈ Finset.range n ∧ (k / (n - k)) = d - 1 := by

  rcases h₁ with ⟨m, hm⟩
  have h2 : m > 0 := by
    nlinarith

  have h2' : d > 0 := by
    by_contra h
    push_neg at h
    have h3 : d = 0 := by linarith
    rw [h3] at hm
    nlinarith

  use (d - 1) * m
  constructor
  · -- Show that (d - 1) * m < n
    have h3 : (d - 1) * m < n := by
      have h4 : (d - 1) * m < d * m := by
        have h5 : d - 1 < d := by 
          omega
        nlinarith [show m > 0 by linarith]
      have h6 : d * m = n := by
        linarith [hm]
      linarith
    simp [Finset.mem_range]
    omega

  · -- Show that ((d - 1) * m) / (n - (d - 1) * m) = d - 1
    have h7 : n - (d - 1) * m = m := by
      have h8 : n = d * m := by linarith [hm]
      have h9 : (d - 1) * m ≤ n := by 
        have h3 : (d - 1) * m < n := by
          have h4 : (d - 1) * m < d * m := by
            have h5 : d - 1 < d := by 
              omega
            nlinarith [show m > 0 by linarith]
          have h6 : d * m = n := by
            linarith [hm]
          linarith
        omega

      have h11 : n = (d - 1) * m + m := by
        have h14 : n = d * m := by linarith [hm]
        cases d with
        | zero => 
          linarith
        | succ d =>
          simp [Nat.mul_add, Nat.add_mul] at h14 ⊢
          all_goals omega

      omega

    rw [h7]

    have h14 : (d - 1) * m / m = d - 1 := by
      have h14 : m > 0 := h2
      have h14' : (d - 1) * m / m = d - 1 := by
        rw [Nat.mul_comm]
        field_simp [h14]
      exact h14'

    simpa using h14