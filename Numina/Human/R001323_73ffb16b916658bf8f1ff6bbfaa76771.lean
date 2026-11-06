import Mathlib

/- The sum of the proper divisors of 18 is 21. What is the sum of the proper divisors of 198? -/
theorem number_theory_23466 (h18: ∑ d ∈ (18:ℕ).properDivisors, d = 21)
  : ∑ d ∈ (198 : ℕ).properDivisors, d = 270 := by
  -- notice that 198 = 11x18 and 11 is a prime number
  have p11: Nat.Prime 11 := by norm_num
  have h198: 198 = 11 * 18 := by norm_num
  -- we claim that for proper divisor of 198, if it is not divided by 11, then it can only be proper divisor of 18 or 18 itself.
  have h1: ∀n ∈ (198:ℕ).properDivisors, 11 ∣ n ∨  n ∣ 18 := by
    intro n hn
    rw [Nat.mem_properDivisors] at hn
    have := hn.left
    rw [h198, Nat.dvd_mul] at this
    rcases this with ⟨y,z,hyz⟩
    by_cases ndv11: 11 ∣ n; tauto
    have hy: y = 1 := by
      have hh1 := hyz.left
      have hh2: y = 1 ∨ y = 11 := by
        exact (Nat.dvd_prime p11).mp hh1
      rcases hh2 with hl | hr
      · exact hl
      · have := hyz.right.right
        rw [hr] at this
        rw [← this] at ndv11
        simp at ndv11
    rw [hy] at hyz; simp at hyz
    rw [hyz.right] at hyz
    tauto
  -- so proper divisors of 198 can be written in two parts.
  let s := (18:ℕ).properDivisors ∪ {18}
  have s_def: s = (18:ℕ).properDivisors ∪ {18} := rfl
  have h2: ∑ d ∈ (198 : ℕ).properDivisors, d =
    ∑ d ∈ ((198 : ℕ).properDivisors \ s), d + ∑ d ∈ s, d := by
    have hh1: (198 : ℕ).properDivisors =
      ((198 : ℕ).properDivisors \ s) ∪ s := by
        have: s ⊆ (198 : ℕ).properDivisors := by
          rw [s_def]
          intro x
          rw [Nat.mem_properDivisors]; simp
          intro hx
          rw [h198]
          rcases hx with hx1 | hx2
          · constructor
            · apply dvd_mul_of_dvd_right hx1.left
            · linarith [hx1.right]
          · rw [hx2]
            constructor
            · apply dvd_mul_of_dvd_right (by simp)
            · linarith
        symm
        apply Finset.sdiff_union_of_subset this
    have hh2: Disjoint ((198 : ℕ).properDivisors \ s) s := by
      exact Finset.sdiff_disjoint
    nth_rw 1 [hh1]
    rw [Finset.sum_union hh2]
  -- and sum over the second part is 11 times sum of properdivisors of 18.
  have h3: ∑ d ∈ ((198 : ℕ).properDivisors \ s), d =
    11 * ∑ d ∈ ((18:ℕ).properDivisors), d := by
    have hh1: 11 * ∑ d ∈ ((18:ℕ).properDivisors), d =
      ∑ d ∈ ((18:ℕ).properDivisors), 11*d := by
      apply Finset.mul_sum
    rw [hh1]
    let i: (a : ℕ) → a ∈ Nat.properDivisors 198 \ s → ℕ :=
      fun a (ha: a ∈ Nat.properDivisors 198 \ s) => a/11
    have i_def: i = fun a (ha: a ∈ Nat.properDivisors 198 \ s)
       => a/11 := rfl
    have h1': ∀a ∈ (Nat.properDivisors 198) \ s, 11 ∣ a ∧ ¬ a ∣ 18
      := by
      intro a ha
      have: a ∈ Nat.properDivisors 198 := by
        have: (Nat.properDivisors 198) \ s ⊆ Nat.properDivisors 198 := by
          exact Finset.sdiff_subset
        exact this ha
      have ha1 := h1 a this
      have ndv18: ¬ a ∣ 18 := by
        by_contra! hc
        have anz: a ≠ 0 := by
          by_contra! az
          rw [az] at hc; simp at hc
        have apos: 0 < a := by
          exact Nat.zero_lt_of_ne_zero anz
        have hh2: a ∈ s := by
          rw [s_def]; simp
          by_cases ha2: a = 18
          · right; exact ha2
          · left
            push_neg at ha2
            have ha3: a ≤ 18 := by
              apply Nat.le_of_dvd (by norm_num) hc
            have ha4: a < 18 := by
              exact Nat.lt_of_le_of_ne ha3 ha2
            exact ⟨hc, ha4⟩
        have hh3: ¬ a ∈ s := by
          rw [Finset.mem_sdiff] at ha
          exact ha.right
        contradiction
      rcases ha1 with hl | hr
      · exact ⟨hl, ndv18⟩
      · exfalso; apply ndv18 hr
    apply Finset.sum_bij i
    · intro a ha
      rw [i_def]; simp
      have ha' := h1' a ha
      rcases ha'.left with ⟨d,hd⟩
      have hhd: a/11 = d := by
        omega
      rw [hhd]
      have a198: a ∈ Nat.properDivisors 198 := by
        have: (Nat.properDivisors 198) \ s ⊆ Nat.properDivisors 198 := Finset.sdiff_subset
        exact this ha
      constructor
      · have tt1: 11 * d ∣ 11 * 18 := by
          rw [← h198, ← hd]
          rw [Nat.mem_properDivisors] at a198
          apply a198.left
        have tt2 : 0 < 11 := by norm_num
        apply Nat.dvd_of_mul_dvd_mul_left tt2 tt1
      · rw [Nat.mem_properDivisors] at a198
        have := a198.right
        rw [hd, h198] at this; linarith [this]
    · intro a1 ha1 a2 ha2
      rw [i_def]; simp
      have a1dv := h1' a1 ha1
      have a2dv := h1' a2 ha2
      rcases a1dv.left with ⟨d1,hd1⟩
      rcases a2dv.left with ⟨d2,hd2⟩
      intro deq
      rw [hd1, hd2] at deq; simp at deq
      rw [hd1, hd2, deq]
    · intro b hb
      use 11*b
      rw [Nat.mem_properDivisors] at hb
      have: 11*b ∈  Nat.properDivisors 198 \ s := by
        have tt1: 11*b ∈ Nat.properDivisors 198 := by
          rw [Nat.mem_properDivisors]
          constructor
          · rw [h198]
            apply mul_dvd_mul (by simp) hb.left
          · rw [h198]
            linarith [hb.right]
        have tt2: 11*b ∉ s := by
          rw [s_def, Nat.properDivisors]; simp
          constructor
          · intro _ _
            have ndv: ¬ 11 ∣ 18 := by norm_num
            by_contra! hc
            have dv: 11 ∣ 18 := by
              apply dvd_of_mul_right_dvd hc
            apply ndv dv
          · omega
        rw [Finset.mem_sdiff]
        exact ⟨tt1,tt2⟩
      use this
      rw [i_def]; simp
    · intro a ha
      rw [i_def]; simp
      have := (h1' a ha).left
      symm; exact Nat.mul_div_cancel' this
  -- thus the answer is sum of 18's properdivisors + 11 x sum of that + 18
  rw [h2, h3, s_def, Finset.sum_union (by simp), h18]
  simp