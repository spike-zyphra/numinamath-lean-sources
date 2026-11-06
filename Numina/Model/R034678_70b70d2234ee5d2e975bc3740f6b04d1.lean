import Mathlib

/- Déterminer tous les entiers a tels que $a-3$ divise $a^{3}-3$. -/

theorem number_theory_607416 : {a : ℤ | a - 3 ∣ a ^ 3 - 3} = {-21,-9,-5,-3,-1,0,1,2,4,5,6,7,9,11,15,27} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume a - 3 divides a ^ 3 - 3, prove that a in the finite set
    intro h
    have h1 : a - 3 ∣ a ^ 3 - 3 := h
    -- So by the definition of division, we can write $a^3 - 3 = k(a - 3)$ for some integer k.
    -- We need to express 24 in terms of $a - 3$ and the multiple.

    have h2 : a - 3 ∣ 24 := by
      have h3 : a - 3 ∣ a ^ 3 - 3 := h1
      -- Express $24$ in terms of $a^3 - 3$ and a multiple of $a - 3$
      have h4 : a - 3 ∣ (a - 3) * (a ^ 2 + 3 * a + 9) := by
        apply dvd_mul_right 
      -- Subtract the two to get 24
      have h5 : a ^ 3 - 3 - ((a - 3) * (a ^ 2 + 3 * a + 9)) = 24 := by
        ring_nf
      have h6 : a - 3 ∣ (a ^ 3 - 3 - ((a - 3) * (a ^ 2 + 3 * a + 9))) := by
        apply Dvd.dvd.sub h3 h4
      rw [h5] at h6
      exact h6
    -- Now we know that $a - 3$ divides 24, so the possible values of a are bounded

    have h3 : a - 3 ≤ 24 := by
      apply Int.le_of_dvd (by norm_num) h2 
    have h4 : a - 3 ≥ -24 := by
      have h5 : - (a - 3) ∣ 24 := by
        exact Int.neg_dvd.2 h2
      have h6 : - (a - 3) ≤ 24 := by
        apply Int.le_of_dvd (by norm_num) h5
      omega 
    -- Now that the bounds are known, we can compute all possible a.

    have h5 : a ≤ 27 := by
      omega 
    have h6 : a ≥ -21 := by
      omega 
    interval_cases a <;> norm_num at h2 ⊢ <;> tauto
  · -- Show that if $a$ is in the finite set, then $a-3$ divides $a^3-3$.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num