import Mathlib

/- On appelle diviseur propre d'un entier $n$ un diviseur positif de $n$ qui est différent de 1 et de n.

Existe-t-il un entier n dont le produit des diviseurs propres est égal à 2013 ? -/
theorem number_theory_607457 {proper_divisor': ℕ → Finset ℕ}
  (proper_divisor'_def: ∀n:ℕ, proper_divisor' n = {d ∈ (Finset.Ioo 1 n) | d ∣ n}) :
  ¬∃ n : ℕ, ∏ d ∈ (proper_divisor' n), d = 2013 := by
  -- the difference of definition here with that of Nat.properDivisors in mathlib
  -- is just whether count 1 in. so product are the same.
  suffices ¬ ∃n:ℕ, ∏ d ∈ n.properDivisors, d = 2013 by
    rintro ⟨n,h⟩
    -- obviously, n cannot be 0 or 1
    have hn: n > 1 := by
      by_contra!
      interval_cases n
      all_goals simp [proper_divisor'_def] at h
    have hh: ∏ d ∈ proper_divisor' n, d = ∏ d ∈ n.properDivisors, d := by
      -- only difference between divisor set defined here and that in mathlib is whether contain 1.
      have h1: n.properDivisors = insert 1 (proper_divisor' n) := by
        ext m
        simp only [proper_divisor'_def n]
        constructor
        · intro h; simp
          by_cases hm: m = 1; · simp [hm]
          right
          replace hm: 1 < m := by
            have: 0 < m := Nat.pos_of_mem_properDivisors h
            omega
          simp at h; simp [h, hm]
        · simp
          rintro (hm1 | hm2); · simp [hm1, hn]
          simp [hm2]
      have h2: 1 ∉ proper_divisor' n := by
        simp [proper_divisor'_def]
      rw [h1, Finset.prod_insert h2]; simp
    rw [← h, hh] at this
    simp at this
  -- back to the problem.
  -- suppose on the contrary, exist such n
  rintro ⟨n, h⟩
  -- notice that 2013 = 3x11x61, so properDivisor of n must contain them
  have h1: ∃ m ∈ n.properDivisors, 3 ∣ m := by
    apply Prime.exists_mem_finset_dvd ?_ ?_
    · apply Nat.prime_iff.mp (by norm_num)
    · rw [h]; norm_num
  have h2: ∃ m ∈ n.properDivisors, 11 ∣ m := by
    apply Prime.exists_mem_finset_dvd ?_ ?_
    · apply Nat.prime_iff.mp (by norm_num)
    · rw [h]; norm_num
  have h3: ∃ m ∈ n.properDivisors, 61 ∣ m := by
    apply Prime.exists_mem_finset_dvd ?_ ?_
    · apply Nat.prime_iff.mp (by norm_num)
    · rw [h]; norm_num
  -- if exist m ∈ properDivisor, p ∣ m, then p ∈ properDivisor
  have mem_of_dvd{p: ℕ}(hm: ∃ m ∈ n.properDivisors, p ∣ m):
    p ∈ n.properDivisors := by
    rcases hm with ⟨m, hm, pdv⟩
    rw [Nat.mem_properDivisors]
    constructor
    · rw [Nat.mem_properDivisors] at hm
      apply Dvd.dvd.trans pdv hm.left
    · have hh1: 0 < m := Nat.pos_of_mem_properDivisors hm
      have hh2: p ≤ m := Nat.le_of_dvd hh1 pdv
      have hh3: m < n := (Nat.mem_properDivisors.mp hm).right
      linarith [hh2, hh3]
  replace h1 := mem_of_dvd h1
  replace h2 := mem_of_dvd h2
  replace h3 := mem_of_dvd h3
  -- therefore 3,11 are properDivisors of n, and follows 33 ∣ n
  have h4: 33 ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    constructor
    · have hh1: 33 = 3 * 11 := by norm_num
      rw [hh1]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ ?_
      · simp at h1; simp [h1]
      · simp at h2; simp [h2]
    · simp at h3
      linarith [h3.right]
  -- so 2013 = prod divided by 3x11x61x33, contradiction
  have: 3*11*61*33 ∣ 2013 := by
    have hh1: {3,11,61,33} ⊆ n.properDivisors := by
      intro m hm
      simp at hm
      rcases hm with (rfl | rfl | rfl | rfl)
      all_goals simp only [h1, h2, h3, h4]
    have hh2: ∏ d ∈ {3,11,61,33}, d ∣ ∏ d ∈ n.properDivisors, d := by
      apply Finset.prod_dvd_prod_of_subset _ _ _ hh1
    simp [h] at hh2
    exact hh2
  norm_num at this