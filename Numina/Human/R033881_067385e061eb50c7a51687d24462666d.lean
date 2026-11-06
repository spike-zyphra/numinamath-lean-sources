import Mathlib
open Nat Finset

/- Prove that any natural number smaller or equal than the factorial of a natural number $ n $ is the sum of at most $ n $ distinct divisors of the factorial of $ n. $ -/
theorem number_theory_26744 {n : ℕ} (hn : n > 0) (k : ℕ) (hk : k ≤ Nat.factorial n) :
    ∃ s : Finset ℕ, s.card ≤ n ∧ ∑ d ∈ s, d = k ∧ ∀ d ∈ s, d ∣ Nat.factorial n := by
  have h₁ : ∀ (n : ℕ), n > 0 → ∀ (k : ℕ), k ≤ Nat.factorial n → ∃ s : Finset ℕ, s.card ≤ n ∧ ∑ d ∈ s, d = k ∧ ∀ d ∈ s, d ∣ Nat.factorial n := by
    intro n hn
    induction' n with n ih
    · -- Base case: $n = 0$.
      exfalso
      linarith
    · -- Inductive step: assume the statement is true for $n$, prove for $n + 1$.
      intro k hk
      by_cases h : n = 0
      · -- Case $n = 0$.
        subst h
        have h₂ : k ≤ 1 := by simpa [Nat.factorial] using hk
        have h₃ : k = 0 ∨ k = 1 := by omega
        cases h₃ with
        | inl h₃ =>
          -- Subcase $k = 0$.
          use ∅
          simp [h₃, Nat.factorial]
        | inr h₃ =>
          -- Subcase $k = 1$.
          use {1}
          simp [h₃, Nat.factorial]
      · -- Case $n > 0$.
        -- Establish $n > 0$ for induction hypothesis.
        have h_n : n > 0 := by omega
        have h_k_bound : k ≤ Nat.factorial n.succ := by simpa [Nat.factorial] using hk
        have h_div_bound : k / n.succ ≤ Nat.factorial n := by
          rw [Nat.factorial_succ] at h_k_bound
          exact Nat.div_le_of_le_mul h_k_bound
        have h_set : ∃ s : Finset ℕ, s.card ≤ n ∧ ∑ d ∈ s, d = k / n.succ ∧ ∀ d ∈ s, d ∣ Nat.factorial n := by
          apply ih h_n _ h_div_bound
        obtain ⟨s, h_card, h_sum, h_dvd⟩ := h_set
        have h_k_eq : k = k % n.succ + n.succ * (k / n.succ) := by
          have h₁ : k = n.succ * (k / n.succ) + k % n.succ := by
            rw [Nat.div_add_mod]
          omega
        have h_nsucc_dvd : n.succ ∣ Nat.factorial n.succ := by
          apply Nat.dvd_of_mod_eq_zero
          simp [Nat.factorial]
        have h_image_dvd : ∀ d ∈ s, n.succ * d ∣ Nat.factorial n.succ := by
          intro d hd
          rw [Nat.factorial_succ]
          exact Nat.mul_dvd_mul (Nat.dvd_refl n.succ) (h_dvd d hd)
        -- Construct new set $s'$ with $card ≤ n + 1$, $sum = k$, and elements dividing $(n + 1)!$.
        have h_set' : ∃ s' : Finset ℕ, s'.card ≤ n.succ ∧ ∑ d ∈ s', d = k ∧ ∀ d ∈ s', d ∣ Nat.factorial n.succ := by
          by_cases h_mod_zero : k % n.succ = 0
          · -- Subcase: $k % n.succ = 0$.
            use s.image (fun d => n.succ * d)
            have h_card_le : (s.image (fun d => n.succ * d)).card ≤ s.card := Finset.card_image_le
            have h_card_n : s.card ≤ n := h_card
            have h_sum_image : ∑ d ∈ s.image (fun d => n.succ * d), d = n.succ * ∑ d ∈ s, d := by
              rw [sum_image]
              · simp [mul_sum]
              · intro x hx y hy h_eq
                exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h_eq
            -- Prove image set sum equals $k$.
            have h_sum_k : ∑ d ∈ s.image (fun d => n.succ * d), d = k := by
              have h₁ : ∑ d ∈ s, d = k / n.succ := h_sum
              have h₂ : k = n.succ * (k / n.succ) := by
                have h₂₀ : k % n.succ = 0 := h_mod_zero
                have h₂₁ : k = n.succ * (k / n.succ) + k % n.succ := by
                  rw [Nat.div_add_mod]
                rw [h₂₀] at h₂₁
                omega
              rw [h_sum_image, h₁, h₂]
              norm_num
            -- Prove elements of image set divide $(n + 1)!$.
            have h_dvd_image : ∀ d ∈ s.image (fun d => n.succ * d), d ∣ Nat.factorial n.succ := by
              intro d hd
              have : ∃ d' ∈ s, d = n.succ * d' := by
                simp [mem_image] at hd
                obtain ⟨a, ha, h_eq⟩ := hd
                exact ⟨a, ha, h_eq.symm⟩
              obtain ⟨d', hd', h₁⟩ := this
              subst h₁
              exact h_image_dvd d' hd'
            exact ⟨by omega, h_sum_k, h_dvd_image⟩
          · -- Subcase: $k % n.succ ≠ 0$.
            use (s.image (fun d => n.succ * d)) ∪ {k % n.succ}
            have h_card_union : (s.image (fun d => n.succ * d) ∪ {k % n.succ}).card ≤ s.card + 1 := by
              calc
                (s.image (fun d => n.succ * d) ∪ {k % n.succ}).card ≤ (s.image (fun d => n.succ * d)).card + 1 := by
                  apply (Finset.card_union_le _ _).trans
                  simp [Finset.card_singleton]
                _ ≤ s.card + 1 := by
                  have : (s.image (fun d => n.succ * d)).card ≤ s.card := Finset.card_image_le
                  omega
            have h_card_n : s.card ≤ n := h_card
            have h_card_nsucc : (s.image (fun d => n.succ * d) ∪ {k % n.succ}).card ≤ n.succ := by omega
            -- Sum over image set equals $n.succ$ * sum over $s$.
            have h_sum_image : ∑ d ∈ s.image (fun d => n.succ * d), d = n.succ * ∑ d ∈ s, d := by
              rw [sum_image]
              · simp [mul_sum]
              · intro x hx y hy h_eq
                exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h_eq
            -- Prove union set sum equals $k$.
            have h_sum_union : ∑ d ∈ s.image (fun d => n.succ * d) ∪ {k % n.succ}, d = k := by
              calc
                ∑ d ∈ s.image (fun d => n.succ * d) ∪ {k % n.succ}, d
                = ∑ d ∈ s.image (fun d => n.succ * d), d + ∑ d ∈ {k % n.succ}, d := by
                  have : Disjoint (s.image (fun d => n.succ * d)) {k % n.succ} := by
                    simp only [disjoint_iff_inter_eq_empty, mem_inter, mem_image, mem_singleton]
                    ext a
                    simp
                    intro d hd h_eq h_contra
                    have : k % n.succ < n.succ := Nat.mod_lt k (Nat.succ_pos n)
                    have : d ≥ 1 := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨h_dvd d hd, Nat.factorial_ne_zero n⟩)
                    have : n.succ * d ≥ n.succ := by
                      have : n.succ * 1 ≤ n.succ * d := Nat.mul_le_mul_left n.succ this
                      simp [Nat.mul_one] at this
                      nlinarith
                    rw [h_eq] at this
                    linarith
                  rw [sum_union this]
                _ = n.succ * ∑ d ∈ s, d + k % n.succ := by rw [h_sum_image, sum_singleton]
                _ = n.succ * (k / n.succ) + k % n.succ := by rw [h_sum]
                _ = k := by
                  rw [add_comm] at h_k_eq
                  exact h_k_eq.symm
            -- Prove $k % n.succ$ divides $(n + 1)!$.
            have h_mod_dvd : k % n.succ ∣ Nat.factorial n.succ := by
              apply Nat.dvd_factorial
              · apply Nat.pos_of_ne_zero
                exact h_mod_zero
              · exact Nat.le_of_lt (Nat.mod_lt k (Nat.succ_pos n))
            have h_dvd_union : ∀ d ∈ s.image (fun d => n.succ * d) ∪ {k % n.succ}, d ∣ Nat.factorial n.succ := by
              intro d hd
              simp [mem_union, mem_image] at hd
              cases hd with
              | inl hd =>
                obtain ⟨d', hd', h_eq⟩ := hd
                rw [← h_eq]
                exact h_image_dvd d' hd'
              | inr hd =>
                rwa [hd]
            exact ⟨h_card_nsucc, h_sum_union, h_dvd_union⟩
        obtain ⟨s', h_card', h_sum', h_dvd'⟩ := h_set'
        exact ⟨s', h_card', h_sum', h_dvd'⟩
  -- Apply induction hypothesis to conclude.
  exact h₁ n hn k hk