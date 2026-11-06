import Mathlib

lemma sub_one_eq {a b : ℚ} : a - b = (a - 1) - (b - 1) := by
  ring

theorem number_theory_244744 (k : ℕ) :
  {n : ℕ | ∀ r ∈ Finset.Icc 1 k, ∃ z : ℤ, (n - (Nat.divisors (n ^ r)).card) / (r : ℚ) = z}.Infinite := by


  let S1 := {n : ℕ | ∀ r ∈ Finset.Icc 1 k, ∃ z : ℤ, (n - (Nat.divisors (n ^ r)).card) / (r : ℚ) = z}
  let S2 := {n : ℕ | 1 ≤ n ∧ ∀ r ∈ Finset.Icc 1 k, r ∣ n - 1}

  have hS2_infinite : S2.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun m => m * Nat.factorial k + 1)
    . intro x y hxy
      simp at hxy
      rcases hxy with h | h
      . exact h
      . have := Nat.factorial_ne_zero k
        contradiction

    . unfold S2
      simp
      intro n r hr1 hr2
      have h1: r ∣ r.factorial := by
        use (r-1).factorial
        rw [Nat.mul_factorial_pred]
        omega
      have h2 := Nat.factorial_dvd_factorial hr2
      have h3 : k.factorial ∣ n * k.factorial := by use n; ring
      have := Nat.dvd_trans h1 h2
      exact Nat.dvd_trans this h3


  have hS2_subset_S1 : S2 ⊆ S1 := by
    unfold S1 S2
    simp
    intro n hn1 hn2 r hr1 hr2
    have ⟨x, hx⟩ := hn2 r hr1 hr2
    field_simp

    have : (Nat.divisors (n ^ r)).card ≡ 1 [MOD r] := by
      by_cases hr_eq_one : r = 1
      . subst r
        exact Nat.modEq_one

      . rw [Nat.card_divisors (by simp; omega)]
        rw [Nat.factorization_pow]
        simp
        have := Nat.mod_modEq (∏ x ∈ (n ^ r).primeFactors, (r * n.factorization x + 1)) r
        rw [Finset.prod_nat_mod] at this
        -- rw [Nat.mul_add_mod_self_left]  -- not in 4.15
        simp [add_comm] at this
        push_neg at hr_eq_one
        rw [← Nat.one_mod_eq_one] at hr_eq_one
        rw [hr_eq_one] at this
        simp at this
        rw [hr_eq_one] at this
        apply Nat.ModEq.symm
        simp [add_comm]
        exact this

    apply Nat.ModEq.symm at this
    apply Nat.ModEq.dvd at this
    obtain ⟨y, hy⟩ := this
    use x - y

    have hy1 : (n ^ r).divisors.card = r * y + 1 := by
      rw [← hy]
      simp
    
    rw [sub_one_eq]
    norm_cast
    rw [hx]
    norm_cast at hy
    rw [hy]

    push_cast
    ring

  -- if S2 ⊆ S1 and S2 is infinite, then S1 is infinite
  exact Set.Infinite.mono hS2_subset_S1 hS2_infinite
