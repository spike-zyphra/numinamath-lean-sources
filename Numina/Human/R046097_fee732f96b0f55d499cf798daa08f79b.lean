import Mathlib

def isGood (n : ℕ) : Prop :=
  ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^n

/- 8. If a positive integer $n$ makes the equation $x^{3}+y^{3}=z^{n}$ have positive integer solutions $(x, y, z)$, then $n$ is called a "good number". Then the number of "good numbers" not exceeding 2019 is $\qquad$ . -/
theorem number_theory_157026 :
    Set.ncard {n | n ≤ 2019 ∧ isGood n} = 1346 := by
    have div_3: ∀ n, isGood n ↔ ¬ 3 ∣ n := by
      intro n
      constructor
      -- By Fermat's Last Theorem, x³ + y³ = z³ has no positive integer solutions
      -- an so any multiples of 3 are not good
      intro h_good
      let ⟨x, y, z, hx, hy, hz, heq⟩ := h_good
      by_contra hdiv
      let ⟨k, hk⟩ := hdiv
      rw [hk] at heq
      rw [show z^(3 * k) = (z^k)^3 from by ring] at heq
      apply fermatLastTheoremThree x y (z^k)
      all_goals try linarith
      apply pow_ne_zero
      linarith
      -- We now show tht if n is not divisible by 3, then the equation does have solutions
      intro hndiv
      -- We find a construction for each possible value of n % 3
      have: n % 3 < 3 := by simp [Nat.mod_lt]
      let k := n/3
      interval_cases hmod: (n % 3)
      -- We are assuming that 3 ∤ n, so n % 3 ≠ 0
      · have := Nat.dvd_iff_mod_eq_zero.mpr hmod
        contradiction
      -- 1^3 + 1^3 = 2^1 => 2^3 + 2^3 = 2^4 => 4^3 + 4^3 = 2^7 => 8^3 + 8^3 = 2^10 => ...
      -- i.e. We have a family of solutions 2^{3k} + 2^{3k} = 2^{3k + 1}, so x = y = 2^k, and z = 2
      · have hn: n = 3*k + 1 := by rw [← Nat.div_add_mod n 3, hmod]
        use 2^k, 2^k, 2
        repeat constructor ; norm_num
        rw [hn]
        ring
      -- 2^3 + 2^3 = 4^2 => 8^3 + 8^3 = 4^5 => 32^3 + 32^3 = 4^8 => ...
      -- i.e. We have a family of solutions 2^{6k + 3} + 2^{6k + 3} = 4^{3k + 2}, so x = y = 2^{2k + 1} and z = 4
      · have hn: n = 3*k + 2 := by rw [← Nat.div_add_mod n 3, hmod]
        use 2^(2*k + 1), 2^(2*k + 1), 4
        repeat constructor ; norm_num
        rw [hn]
        ring_nf
        rw [show 6 = 2 * 3 from rfl]
        rw [← mul_assoc, mul_comm k, mul_assoc, pow_mul]
        rfl
    -- We count the multiple of 3 below 2019 by noting that they are equal to 3*1, 3*2, 3*3, ..., 3*673
    -- and so there are 673 of them
    let mul_3: ℕ ↪ ℕ := {
      toFun: ℕ → ℕ := λ n ↦ 3 * n
      inj': ∀ a b: ℕ, 3*a = 3*b → a = b := by
        intro a b h_eq
        rw [Nat.mul_right_inj (by decide)] at h_eq
        assumption
    }
    -- The good natural numbers below 2020 are obtained by taking the natural numbers from
    -- 1 to 2019 and removing the multiples of 3
    let fin := (Finset.range 2020) \ (Finset.map mul_3 (Finset.range 674))
    have: {n | n ≤ 2019 ∧ isGood n} = fin.toSet := by
      unfold fin
      ext x
      simp
      constructor
      intro ⟨x_bound, x_good⟩
      constructor
      linarith
      intro k _
      by_contra h_mul
      have: 3 ∣ x := by
        simp [mul_3] at h_mul
        exact dvd_of_mul_right_eq k h_mul
      rw [div_3] at x_good
      contradiction
      intro ⟨x_bound, h⟩
      constructor
      linarith
      rw [div_3]
      by_contra h_mul
      let ⟨k, hk⟩ := h_mul
      simp [mul_3] at h
      exact (h k (by linarith)) hk.symm
    rw [this]
    simp [Set.ncard_eq_toFinset_card fin.toSet fin.toSet.toFinite]
    unfold fin
    -- Now the number of good numbers not exceeding 2019 is 2019 minus the number of
    -- multiples of 3 up to 2019
    rw [Finset.card_sdiff]
    simp
    apply Finset.subset_iff.mpr
    simp [mul_3]
    intro x x_bound
    linarith