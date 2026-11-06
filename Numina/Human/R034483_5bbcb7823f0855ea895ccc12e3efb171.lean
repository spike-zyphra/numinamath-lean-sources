import Mathlib

/- For how many ordered pairs of positive [integers](https://artofproblemsolving.com/wiki/index.php/Integer) $(x,y),$ with $y < x ≤ 100,$ is it true that $\frac{x}{y}$ is an integer and $\frac{x+1}{y+1}$ is also an integer? -/

theorem number_theory_96531 : { (x, y) : ℕ × ℕ | 1 <= y ∧ y < x ∧ x ≤ 100 ∧ y ∣ x ∧ (y + 1) ∣ (x + 1) }.ncard = 85 := by

  -- We will show that the set of pairs (x, y) as in the problem statement is the image of the function
  -- z ↦ (z * y * (y + 1) + y, y) for y in the range [1, 100] and z in the range [1, (100 - y) / (y * (y + 1))].
  have bijection : { (x, y) : ℕ × ℕ | 1 <= y ∧ y < x ∧ x ≤ 100 ∧ y ∣ x ∧ (y + 1) ∣ (x + 1) }
      = (Finset.biUnion (Finset.Icc 1 100) fun y ↦ Finset.image (fun z ↦ (⟨z * y * (y + 1) + y, y⟩))
      (Finset.Icc 1 ((100 - y) / (y * (y + 1))))).toSet := by
    ext ⟨x, y⟩
    constructor
    · -- First we show that the pairs (x, y) as in the problem statement are in the image of the function
      -- z ↦ (z * y * (y + 1) + y, y).
      simp only [Set.mem_setOf_eq, Finset.coe_biUnion, Finset.coe_Icc, Set.mem_Icc,
      Finset.coe_image, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, exists_prop, and_imp]
      intro hy hxy hx ⟨k, hk⟩ ⟨k', hk'⟩
      -- y is the same as the second element of the pair
      use y
      refine ⟨⟨hy, le_of_lt (lt_of_lt_of_le hxy hx)⟩, ?_⟩
      -- The key of the proof is to show that $y ⬝ (y + 1) ∣ (x - y)$.
      have div_prod : y * (y + 1) ∣ (x - y) := by
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        · exact (Nat.coprime_add_iff_right (Nat.dvd_refl y)).mpr (Nat.gcd_one_right y)
        · use (k-1); rw [mul_tsub, mul_one, ← hk]
        · use (k'-1); rw [mul_tsub, mul_one, ← hk']; simp
      -- Now (x, y) is the image of ((k - k') * y * (y + 1) + y, y).
      use k - k'
      have : k - k' = (x - y) / ((y * (y + 1))) := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hy (Nat.add_pos_left hy 1))
        rw [tsub_mul, ← mul_assoc, ← mul_assoc, mul_comm k y, mul_comm k' y, mul_assoc y k' _,
          mul_comm k' _, ← hk, ← hk', mul_add, mul_add, mul_one, mul_one, Nat.sub_add_eq,
          mul_comm y x, Nat.add_sub_self_left]
        exact Eq.symm (Nat.div_mul_cancel div_prod)
      refine ⟨⟨?_, ?_⟩, ?_, rfl⟩
      · rw [this]
        obtain ⟨r, hr⟩ := div_prod
        rw [hr, mul_comm, Nat.mul_div_cancel]
        · by_contra!
          rw [Nat.lt_one_iff] at this
          rw [this, mul_zero] at hr
          omega
        · exact (Nat.mul_pos hy (Nat.add_pos_left hy 1))
      · rw [this]; exact Nat.div_le_div_right (Nat.sub_le_sub_right hx y)
      · calc
          (k - k') * y * (y + 1) + y
            = x * (y + 1) - y * (x + 1) + y := by rw [tsub_mul, tsub_mul, mul_comm k y,
              mul_comm k' y, mul_assoc y k' _, mul_comm k' _, ← hk, ← hk']
          _ = (x * y + x) - (y * x + y) + y := by rw [mul_add, mul_add, mul_one, mul_one]
          _ = (x * y + x - y * x - y) + y := by rw [Nat.sub_add_eq]
          _ = (x * y - y * x + x - y) + y := by rw [mul_comm y x, Nat.sub_self, zero_add, Nat.add_sub_self_left]
          _ = (0 + x - y) + y := by rw [Nat.mul_comm x y, Nat.sub_self]
          _ = x - y + y := by rw [zero_add]
          _ = x := by rw [Nat.sub_add_cancel (Nat.le_of_lt hxy)]
    · -- Now we show that all pairs (x, y) in the image of the function satisfy the conditions of the problem.
      simp only [Finset.coe_biUnion, Finset.coe_Icc, Set.mem_Icc, Finset.coe_image, Set.mem_iUnion,
      Set.mem_image, Prod.mk.injEq, exists_prop, Set.mem_setOf_eq, forall_exists_index, and_imp]
      intro w h1 h100 z hz hwz hx hy
      rw [hy] at h1 h100 hwz hx
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact h1
      · rw [← hx]
        apply lt_add_of_pos_left
        exact Nat.mul_pos (Nat.mul_pos hz h1) (Nat.add_pos_left h1 1)
      · rw [← mul_le_mul_right (Nat.mul_pos h1 (Nat.add_pos_left h1 1))] at hwz
        have := le_trans hwz (Nat.div_mul_le_self  (100 - y) (y * (y + 1)))
        rw [← add_le_add_iff_right y, ← mul_assoc, hx, Nat.sub_add_cancel h100] at this
        exact this
      · use z * (y + 1) + 1; rw [← hx]; ring
      · use z * y + 1; rw [← hx]; ring

  -- Now we can count the number of pairs (x, y) in the image of the function.
  have sum_85 : ∑ y ∈ Finset.Icc 1 100, (100 - y) / (y * (y + 1)) = 85 := by decide

  -- The only thing left to do is to show that the function is injective and that the union is disjoint.
  rw [bijection, ← sum_85, Set.ncard_eq_toFinset_card']
  simp only [Finset.coe_biUnion, Finset.coe_Icc, Set.mem_Icc, Finset.coe_image, Finset.toFinset_coe]
  rw [Finset.card_biUnion ?_]
  · -- The function is injective, as on the second element of the pair it is the identity.
    congr; ext y
    rw [Finset.card_image_of_injOn ?_, Nat.card_Icc]
    · rfl
    · intro a ha b hb h
      simp only [Prod.mk.injEq, add_left_inj, mul_eq_mul_right_iff, AddLeftCancelMonoid.add_eq_zero,
        one_ne_zero, and_false, or_false, and_true] at h
      rcases h with h | h
      · exact h
      · simp [h] at ha hb
  · -- The disjointness of the union is trivial, as the second element of the pair is the index of the union.
    intro x hx y hy hxy
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ h ⟨a', b'⟩ h'
    simp only [Finset.mem_image, Finset.mem_Icc] at h h'
    rcases h with ⟨k, _, hk⟩
    rcases h' with ⟨k', _, hk'⟩
    rw [← hk, ← hk']
    simp [hxy]