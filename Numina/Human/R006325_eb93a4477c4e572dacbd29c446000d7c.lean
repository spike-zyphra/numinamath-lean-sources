import Mathlib

/- Let $k_1, k_2, k_3, d$ be positive integers. Let $r_1 = k_1/d$, $r_2 = k_2/d$, and $r_3 = k_3/d$ be three positive rational numbers.
Let $S$ be the set of real numbers $x$ such that there exist positive natural numbers $a, b, c$ for which $x = a \cdot r_1$, $x = b \cdot r_2$, and $x = c \cdot r_3$.
Show that the least element of $S$ is $\frac{\text{LCM}(k_1, k_2, k_3)}{d}$. -/
theorem number_theory_635891 {k1 k2 k3 d: ℕ}
  (h: 0 < k1 ∧ 0 < k2 ∧ 0 < k3 ∧ 0 < d):
  IsLeast {x:ℝ | ∃ (a b c: ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧
    x = a * (k1/d:ℚ) ∧ x = b * (k2/d:ℚ) ∧ x = c * (k3/d:ℚ)}
    (Finset.lcm ({k1,k2,k3}: Finset ℕ) id / d: ℝ) := by

  -- by definition of lcm, k1, k2, k3 divide their lcm.
  have h1: k1 ∣ Finset.lcm ({k1,k2,k3}: Finset ℕ) id := by
    nth_rw 1 [show k1 = id k1 by simp]
    apply Finset.dvd_lcm (by simp)
  have h2: k2 ∣ Finset.lcm ({k1,k2,k3}: Finset ℕ) id := by
    nth_rw 1 [show k2 = id k2 by simp]
    apply Finset.dvd_lcm (by simp)
  have h3: k3 ∣ Finset.lcm ({k1,k2,k3}: Finset ℕ) id := by
    nth_rw 1 [show k3 = id k3 by simp]
    apply Finset.dvd_lcm (by simp)
  have lcm_pos: 0 < Finset.lcm ({k1,k2,k3}: Finset ℕ) id := by
    refine Nat.pos_of_ne_zero ?_
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    simp [ne_of_lt, h]

  rw [IsLeast, lowerBounds]
  simp only [Rat.cast_div, Rat.cast_natCast, exists_and_left,
  normalize_eq, Set.mem_setOf_eq, forall_exists_index, and_imp]
  constructor

  · -- verify lcm / d satisfy the condition.
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    rcases h3 with ⟨c, hc⟩
    have apos: 0 < a := by
      rw [ha] at lcm_pos
      exact Nat.pos_of_mul_pos_left lcm_pos
    have bpos: 0 < b := by
      rw [hb] at lcm_pos
      exact Nat.pos_of_mul_pos_left lcm_pos
    have cpos: 0 < c := by
      rw [hc] at lcm_pos
      exact Nat.pos_of_mul_pos_left lcm_pos
    refine ⟨a, apos, b, bpos, c, cpos, ?_⟩
    nth_rw 1 [ha, hb, hc]
    push_cast
    ring_nf
    trivial

  · -- show lcm / d is a lower bound.
    rintro _ a apos b bpos c cpos rfl hab hac
    have dpos := h.right.right.right
    rify at dpos
    -- a (k1/d) = b (k2/d), so a k1 = b k2
    have hab': a*k1 = b*k2 := by
      field_simp [dpos] at hab
      norm_cast at hab
    have hac': a*k1 = c*k3 := by
      field_simp [dpos] at hac
      norm_cast at hac
    rw [← mul_div_assoc]
    rw [div_le_div_iff_of_pos_right dpos]
    norm_cast
    refine Nat.le_of_dvd (mul_pos apos h.left) ?_
    apply Finset.lcm_dvd ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, id_eq,
    forall_eq_or_imp, dvd_mul_left, forall_eq, true_and]
    nth_rw 1 [hab', hac']
    simp only [dvd_mul_left, and_self]