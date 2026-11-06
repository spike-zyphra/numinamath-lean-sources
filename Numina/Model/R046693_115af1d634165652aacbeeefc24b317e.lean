import Mathlib


open Finset


theorem number_theory_102878 (S : Finset ℕ) (hS : S.card = 2020) :
    Odd (∑ n ∈ S, n) → Even (∏ n ∈ S, n) := by
  intro h_odd_sum
  have h1 : S.card % 2 = 0 := by
    omega
  have h7 : ∃ x ∈ S, Even x := by
    by_contra h4
    push_neg at h4
    -- Assume no such x exists, which means all x in S are odd
    have h8 : ∀ x, x ∈ S → Odd x := by
      intro x hx
      have h9 : ¬ (Even x) := h4 x hx
      simp at h9 ⊢
      try { tauto }
    -- Now, with all elements being odd, we show that the sum must be even
    have h88 : (∑ n in S, n) % 2 = 0 := by
      have h46 : ∀ x ∈ S, Odd x := h8
      have h34 : ∀ x ∈ S, x % 2 = 1 := by
        intro x hx
        have hx2 : Odd x := h46 x hx
        rcases hx2 with ⟨m, hm⟩
        omega
      have h65 : (S.sum (fun (n : ℕ) => n ) ) % 2 = 0 := by
        have eq1 : (S.sum (fun (n : ℕ) => n)) % 2 = (S.sum (fun (n : ℕ) => (n % 2) ) ) % 2 := by
          simp [Finset.sum_nat_mod]
        rw [eq1]
        have eq2 : S.sum (fun (n : ℕ) => (n % 2)) = S.card := by
          have h89 : ∀ x ∈ S, (x % 2 )= 1 := by
            intro x hx
            have h87 : x % 2 = 1 := h34 x hx
            simpa using h87
          calc
            S.sum (fun (n : ℕ) => (n % 2))
                = ∑ x in S, (1 : ℕ) := by
                  apply Finset.sum_congr rfl h89
            _ = S.card := by
              simp
        rw [eq2, hS]
        all_goals omega
      exact h65
    -- We have that the sum is odd (our hypothesis) and we just proved the sum is even, which is a contradiction
    rcases h_odd_sum with ⟨k, hk⟩
    have h90 : (S.sum (fun (n : ℕ) => n ) ) % 2 = 1 := by
      omega
    omega
  -- Now, apply the lemma we found earlier
  rcases h7 with ⟨x, hx7, hx8⟩
  have hx5 : x ∈ S := hx7
  have hx9 : Even x := hx8
  rcases hx9 with ⟨m, hm⟩
  -- Now, show that x divides the product and 2 divides x
  have hx87 : 2 ∣ (∏ n in S, n) := by
    have hx0 : x ∣ (∏ n in S, n) := by
      apply Finset.dvd_prod_of_mem
      exact hx5
    have hx6 : 2 ∣ x := by
      use m
      all_goals omega
    exact dvd_trans hx6 hx0
  -- Now convert this to the form we need
  rcases hx87 with ⟨k, hk⟩
  exact ⟨k, by linarith⟩