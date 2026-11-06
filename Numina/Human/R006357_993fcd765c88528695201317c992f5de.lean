import Mathlib

set_option maxHeartbeats 1000000

-- Let $N$ be a positive integer. Determine the number of ordered triples $(a,b,c)$ of positive integers such that $a$ divides $b$, $a$ divides $c$, and $a+b+c=N$. Show that this number is equal to $\sum_{d|N, d \ge 3} (d-2)$, where the sum is over all positive divisors $d$ of $N$ such that $d \ge 3$.

theorem my_favorite_theorem (N : ℕ) (hN : N > 0) :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ∣ b ∧ a ∣ c ∧ a + b + c = N}.ncard =
    ∑ d ∈ N.divisors \ {1, 2}, (d - 2) := by

  let S := {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ∣ b ∧ a ∣ c ∧ a + b + c = N}
  let T := Finset.filter (fun x => x.1 > 0 ∧ x.2.1 > 0 ∧ x.2.2 > 0
    ∧ x.1 ∣ x.2.1 ∧ x.1 ∣ x.2.2 ∧ x.1 + x.2.1 + x.2.2 = N)
    ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))

  have hST : S = T := by
    ext ⟨a, b, c⟩
    unfold S T
    simp
    intro h1 h2 h3 h4 h5 h6
    omega

  suffices S.ncard = ∑ d ∈ N.divisors \ {1, 2}, (d - 2) from this
  rw [hST]
  simp

  let f : ℕ × ℕ × ℕ → ℕ := fun x => N/x.1
  have := Finset.card_eq_sum_card_image f T
  rw [this]

  have : Finset.image f T = N.divisors \ {1, 2} := by
    unfold T
    ext d
    simp
    constructor
    . rintro ⟨a, b, c, ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hc1, hc2⟩, ha, hb, hc, hab, hac, hsum⟩, hf⟩
      unfold f at hf
      simp at hf
      obtain ⟨m, hm⟩ := hab
      obtain ⟨n, hn⟩ := hac
      have : 2 < d := by
        have : d = 1 + m + n := by
          rw [hm, hn] at hsum
          rw [show N = a*d by
            rw [← hf]
            rw [Nat.mul_div_cancel']
            use (1 + m + n)
            rw [← hsum]
            ring
          ] at hsum
          nlinarith

        have : 1 ≤ m := by
          by_contra h
          simp at h
          subst m
          simp at hm
          omega

        have : 1 ≤ n := by
          by_contra h
          simp at h
          subst n
          simp at hn
          omega

        omega

      refine ⟨⟨?_, by omega⟩, by omega, by omega⟩
      use a
      rw [← hf]
      rw [Nat.div_mul_cancel]
      use 1 + m + n
      rw [← hsum]
      rw [hm]
      rw [hn]
      ring

    . intro ⟨⟨h1, h2⟩, hd_ne_1, hd_ne_2⟩
      obtain ⟨a, ha⟩ := h1

      have ha_ne_zero : a ≠ 0 := by
        by_contra h
        subst a
        simp at ha
        contradiction

      have ha_le_N : a ≤ N := by
        apply Nat.le_of_dvd hN
        use d
        rw [ha]
        ring

      have h2_lt_d : 2 < d := by
        by_contra h
        interval_cases d
        . simp at ha
          contradiction
        . simp at hd_ne_1
        . simp at hd_ne_2

      use a
      use a
      use a*(d-2)
      split_ands
      all_goals try simp
      all_goals try omega
      . by_contra h
        simp at h
        omega
      . rw [ha]
        let e := d - 2
        have : d = 2 + e := by omega
        rw [this]
        simp
        ring_nf
        omega

      . ring_nf
        rw [← mul_add]
        rw [show 2 + (d - 2) = d by omega]
        rw [ha]
        ring
      . unfold f
        simp
        rw [ha]
        rw [Nat.mul_div_cancel]
        omega

  rw [this]
  apply Finset.sum_congr rfl
  intro d hd
  let a := N / d

  have hN_eq : N = a*d := by
    unfold a
    rw [Nat.div_mul_cancel]
    simp at hd
    exact hd.1.1

  have ha_ne_zero : a ≠ 0 := by
    by_contra h
    rw [h] at hN_eq
    simp at hN_eq
    omega

  have h_1_le_a : 1 ≤ a := by
    by_contra h
    simp at h
    contradiction

  have hd_eq : d = N / a := by
    rw [hN_eq]
    rw [Nat.mul_div_cancel_left]
    omega

  have ha_le_N : a ≤ N := by
    apply Nat.le_of_dvd hN
    use d

  unfold T
  rw [Finset.filter_filter]
  let g : (i : ℕ) → i < d - 2 → ℕ × ℕ × ℕ := fun i hi => (a, a*(i+1), a*(d-2-i))
  apply Finset.card_eq_of_bijective g
  . intro x hx
    unfold f at hx
    simp at hx
    obtain ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hc1, hc2⟩, ⟨ha, hb, hc, hab, hac, hsum⟩, heq⟩ := hx

    obtain ⟨m, hm⟩ := hab
    obtain ⟨n, hn⟩ := hac

    have hm_ne_zero : m ≠ 0 := by
      by_contra h
      subst m
      simp at hm
      omega

    have hn_ne_zero : n ≠ 0 := by
      by_contra h
      subst n
      simp at hn
      omega

    have heq' : N = x.1 * d := by
      rw [← heq]
      rw [Nat.mul_div_cancel']
      use 1 + m + n
      rw [← hsum]
      rw [hm]
      rw [hn]
      ring

    have ha_x1 : a = x.1 := by
      rw [hN_eq] at heq'
      nlinarith

    let i := m - 1
    have ha_x2 : a * (i + 1) = x.2.1 := by
      unfold i
      rw [show m - 1 + 1 = m by omega]
      rw [hm]
      rw [ha_x1]

    have ha_x3 : a * (d - 2 - i) = x.2.2 := by
      rw [show d - 2 - i = (d-1) - (i+1) by omega]
      rw [Nat.mul_sub]
      rw [ha_x2]
      rw [Nat.mul_sub]
      omega

    have hi : i < d - 2 := by
      by_contra h
      simp at h
      nlinarith

    use i, hi
    unfold g
    apply Prod.ext
    . simp
      exact ha_x1
    . apply Prod.ext
      . simp
        exact ha_x2
      . simp
        exact ha_x3

  . intro i hi
    unfold f g
    simp

    let e := (d - 2 - i)
    have he1 : e = d - 2 - i := rfl
    have he2 : d = 2 + i + e := by omega

    split_ands
    all_goals try omega
    . by_contra h
      simp at h
      contradiction
    . rw [hN_eq]
      nlinarith
    . by_contra h
      simp at h
      omega
    . rw [← he1]
      rw [hN_eq]
      rw [he2]
      nlinarith
    . rw [← he1]
      rw [hN_eq]
      rw [he2]
      ring

  . intro i j hi hj hg
    unfold g at hg
    simp at hg
    omega
