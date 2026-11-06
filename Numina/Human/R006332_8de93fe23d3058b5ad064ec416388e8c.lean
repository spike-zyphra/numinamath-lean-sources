import Mathlib

theorem number_theory_635964
  (a b n K : ℕ) (hK : Even K ∧ K > 0) (h : ∃ m, m^2 = a^2 + K * n * b^2) :
  ∃ c d, a^2 + (K / 2) * n * b^2 = c^2 + d^2 := by 
  obtain ⟨keven, kpos⟩ := hK
  obtain ⟨x, hx⟩ := h
  zify at hx
  obtain ⟨k0, hk0⟩ := keven
  have eq1 : (x - a : ℤ) * (x + a) = 2 * k0 * n * b ^ 2 := by
    rw [hk0] at hx
    ring_nf
    ring_nf at hx
    norm_num at hx
    linarith
  have h1 : ∃ (u : ℤ), x - a = 2 * u := by
    have even_aux : Even ((x : ℤ) - a) := by 
      by_contra hc
      simp at hc
      have odd1 : Odd ((x : ℤ) + a) := by 
        have aux : ((x : ℤ) + a) = ((x : ℤ) - a) + 2 * a := by 
          ring
        rw [aux]
        refine Even.odd_add ?_ hc
        use (a)
        ring
      have dvd1 : 2 ∣ ((x : ℤ) - a) * ((x : ℤ) + a)  := by 
        rw [eq1]
        use k0 * n * b ^ 2
        ring
      have dvd_or : 2 ∣ ((x : ℤ) - a) ∨ 2 ∣ ((x : ℤ) + a) := by
        refine Prime.dvd_or_dvd (by norm_num) dvd1
      obtain dvd2 | dvd2 := dvd_or
      · -- If 2 divides ((x : ℤ) - a), then this contradicts to Odd ((x : ℤ) - a)
        have : ¬Odd ((x : ℤ) - a) := by
          refine Int.not_odd_iff_even.mpr ?_
          exact (even_iff_exists_two_nsmul ((x : ℤ) - ↑a)).mpr dvd2
        contradiction
      · -- If 2 divides ((x : ℤ) + a), then this contradicts to Odd ((x : ℤ) + a)
        have : ¬ Odd ((x : ℤ) + a) := by 
          refine Int.not_odd_iff_even.mpr ?_
          exact (even_iff_exists_two_nsmul ((x : ℤ) + ↑a)).mpr dvd2
        contradiction
    obtain ⟨u, hu⟩ := even_aux
    use u
    rw [hu]
    ring
  have h2 : ∃ (v : ℤ), x + a = 2 * v := by 
    have even_aux : Even ((x : ℤ) + a) := by 
      by_contra hc
      simp at hc
      have odd1 : Odd ((x : ℤ) - a) := by 
        have aux : ((x : ℤ) - a) = ((x : ℤ) + a) - 2 * a := by 
          ring
        rw [aux]
        refine Even.odd_add ?_ hc
        use (-a)
        ring
      have dvd1 : 2 ∣ ((x : ℤ) - a) * ((x : ℤ) + a)  := by 
        rw [eq1]
        use k0 * n * b ^ 2
        ring
      have dvd_or : 2 ∣ ((x : ℤ) - a) ∨ 2 ∣ ((x : ℤ) + a) := by
        refine Prime.dvd_or_dvd (by norm_num) dvd1
      obtain dvd2 | dvd2 := dvd_or
      · -- If 2 divides ((x : ℤ) - a), then this contradicts to Odd ((x : ℤ) - a)
        have : ¬Odd ((x : ℤ) - a) := by
          refine Int.not_odd_iff_even.mpr ?_
          exact (even_iff_exists_two_nsmul ((x : ℤ) - ↑a)).mpr dvd2
        contradiction
      · -- If 2 divides ((x : ℤ) + a), then this contradicts to Odd ((x : ℤ) + a)
        have : ¬ Odd ((x : ℤ) + a) := by 
          refine Int.not_odd_iff_even.mpr ?_
          exact (even_iff_exists_two_nsmul ((x : ℤ) + ↑a)).mpr dvd2
        contradiction
    obtain ⟨u, hu⟩ := even_aux
    use u
    rw [hu]
    ring
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  have eq2 : 2 * u * v = k0 * n * b ^ 2 := by
    rw [hu, hv] at eq1
    linarith
  rw [hu, hv] at eq1
  have h3 : ∃ (u' : ℕ), u = u' := by
    use u.toNat
    refine Eq.symm (Int.toNat_of_nonneg ?_)
    have xgea : x ≥ a := by 
      norm_cast at hx
      have xsq_ge : x ^ 2 ≥ a ^ 2 := by 
        rw [hx]
        omega
      by_contra hc
      simp at hc 
      have neq2 : 2 ≠ 0 := by 
        norm_num
      obtain aux := Nat.pow_lt_pow_left hc neq2
      linarith
    linarith
  have h4 : ∃ (v' : ℕ), v = v' := by
    use v.toNat
    refine Eq.symm (Int.toNat_of_nonneg ?_)
    have aux : x + (a : ℤ) ≥ 0 := by 
      norm_cast
      linarith
    linarith
  obtain ⟨u', hu'⟩ := h3
  obtain ⟨v', hv'⟩ := h4
  use u', v'
  have aux1 : K / 2 = k0 := by 
    rw [hk0]
    omega
  rw [aux1]
  zify
  have aeq : a = (v - u) := by 
    linarith
  rw [aeq, ←hu', ←hv', ←eq2]
  ring