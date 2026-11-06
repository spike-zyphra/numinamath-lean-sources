import Mathlib


/-
Determine whether there exist an infinite number of  positive integers   $x,y $  satisfying the condition:  $x^2+y \mid x+y^2.$   Please prove it.
-/


theorem number_theory_8969 :
    { (x, y) : ℤ × ℤ | 0 < x ∧ 0 < y ∧ x ^ 2 + y ∣ x + y ^ 2 }.Infinite := by

  -- Putting  $y=kx$  where  $k$  is positive integer we have that  $ x^2+kx \mid x+k^2x^2 $  from which we deduce  $ x+k \mid k^2x+1=x(k^2-x^2)+x^3+1 $  so  $ x+k \mid x^3+1 $ . So we can now put  $k=x^3-x+1$  so pair  $(x,y)=(a,a(a^3-a+1))$  works for every integer  $a \geq 2$  so there are infinitely many solutions.

  set ts := { (x, y) : ℤ × ℤ | 0 < x ∧ 0 < y ∧ x^2 + y ∣ x + y^2 } with hts
  set s := { (a, b) : ℤ × ℤ | 2 ≤ a ∧ b = a * (a ^ 3 - a + 1) } with hs

  -- s is infinite
  have h_s_inf : s.Infinite := by
    rw [hs]

    refine Set.infinite_of_forall_exists_gt ?h
    intro ⟨x, y⟩
    set mx := max x y
    set nx := mx * mx + 2 with hnx
    set ny := nx * (nx ^ 3 - nx + 1) with hny
    use ⟨nx, ny⟩

    have r0 : mx < nx := by
      rw [hnx]
      by_cases h : 0 ≤ mx
      . by_cases hh : mx = 0
        . simp [hh]
        have r1 : 0 < mx := lt_of_le_of_ne h fun a => hh (id (Eq.symm a))
        have r2 : mx ≤ mx * mx := le_mul_of_one_le_left h r1
        refine Int.lt_add_of_le_of_pos r2 (by linarith)
      . simp at h
        have : 0 < mx * mx + 2 := Int.add_pos_of_nonneg_of_pos (mul_self_nonneg mx) (by linarith)
        exact Int.lt_trans h this

    have r1 : 2 ≤ nx := by
      exact Int.le_add_of_nonneg_left (mul_self_nonneg mx)

    have r2 : x < nx := by
      exact Int.lt_of_le_of_lt (Int.le_max_left x y) r0

    have r3 : y < ny := by
      apply Int.lt_of_lt_of_le (Int.lt_of_le_of_lt (Int.le_max_right x y) r0)
      rw [hny, mul_add, mul_one]
      apply Int.le_add_of_nonneg_left
      rw [show nx * (nx ^ 3 - nx) = nx ^ 2 * (nx ^ 2 - 1) by ring_nf]
      have t1 : 0 < nx ^ 2 := by
        have : 0 ≤ nx ^ 2 := by exact sq_nonneg nx
        by_contra h
        have : nx ^ 2 = 0 := by linarith
        obtain ⟨h, _⟩ := pow_eq_zero_iff'.mp this
        linarith
      exact (mul_nonneg_iff_of_pos_left t1).mpr (Int.sub_nonneg_of_le t1)

    simp [r1 ,r2, r3]
    left; linarith

  -- s is subset of ts
  have h_s_in : s ⊆ ts := by
    rw [hts, hs]
    simp
    intro a ha

    have r1 : a ^ 2 + a * (a ^ 3 - a + 1) ∣ a + (a * (a ^ 3 - a + 1)) ^ 2 := by
      have : a + (a * (a ^ 3 - a + 1)) ^ 2 = (1 + a - 2 * a ^ 2 + a ^ 4) * (a ^ 2 + a * (a ^ 3 - a + 1)) := by ring_nf
      rw [this]
      exact dvd_mul_left _ _

    have r2 : 0 < a := by linarith

    have r3 : 0 < a ^ 3 - a + 1  := by
      have r31 : 0 < a ^ 2 - 1 := by
        refine Int.sub_pos.mpr ?_
        refine (one_lt_sq_iff (by linarith)).mpr ha
      rw [show a ^ 3 - a = a * (a ^ 2 - 1) by ring_nf]
      refine Int.lt_add_one_iff.mpr ?_
      refine (Int.mul_nonneg_iff_of_pos_right r31).mpr (by linarith)

    simp_all

  have h_ts_inf : ts.Infinite := by
    rw [hts]
    exact Set.Infinite.mono h_s_in h_s_inf

  exact h_ts_inf
