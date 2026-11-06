import Mathlib

open Nat


/- 3. Solve the equation $x!+y!+z!=u!$ in $\mathbb{N}$. -/
theorem number_theory_216943 {x y z u: ℕ}:
  x ! + y ! + z ! = u ! ↔ (x=2 ∧ y=2 ∧ z=2 ∧ u=3) := by

  -- let m be max of x,y,z
  let m := max x (max y z)
  have mx: m ≥ x := Nat.le_max_left x _
  have my: m ≥ y := by
    have := Nat.le_max_left y z
    apply this.trans (Nat.le_max_right x _)
  have mz: m ≥ z := by
    have := Nat.le_max_right y z
    apply this.trans (Nat.le_max_right x _)

  have hm: m = x ∨ m = y ∨ m = z := by
    simp only [m]
    rcases max_choice y z with hyz | hyz
    <;> simp only [hyz]
    · rcases max_choice x y with hxy | hxy
      <;> simp [hxy]
    · rcases max_choice x z with hxz | hxz
      <;> simp [hxz]

  -- u ! cannot be 3
  have fac_ne {u:ℕ}: u ! ≠ 3 := by
    rintro heq
    have h1: u ! > 2 ! := by
      norm_num [heq]
    replace h1: u > 2 := by
      by_contra!
      absurd h1
      push_neg
      exact factorial_le this
    have h2: u ! < 3 ! := by
      norm_num [heq, factorial_succ]
    replace h2: u < 3 := by
      by_contra!
      absurd h2
      push_neg
      exact factorial_le this
    omega


  constructor
  · intro heq
    -- notice that u ! = u (u-1)! ≤ 3 (max x y z)!
    -- but u > max (x y z), so u ≥ max (x y z) + 1.
    -- so max (x y z) + 1 ≤ u ≤ 3.
    have hum1: u ! > m ! := by
      rcases hm with (hm | hm | hm)
      all_goals
        rw [← heq, hm]
        linarith only [factorial_pos x, factorial_pos y,
        factorial_pos z]
    replace hum1: u > m := by
      by_contra!
      absurd hum1
      push_neg
      exact factorial_le this
    have uge: u ≥ m+1 := by exact hum1
    replace hum1: u ! ≥ (m+1) * m ! := by
      rw [← factorial_succ]
      exact factorial_le uge
    have hum2': u ! ≤ 3 * m ! := by
      rw [← heq]
      linarith only [factorial_le mx, factorial_le my,
      factorial_le mz]
    replace hum2 := hum1.trans hum2'
    replace hum2: (m+1) ≤ 3 := by
      exact Nat.le_of_mul_le_mul_right hum2 (factorial_pos m)
    replace hum2: m ≤ 2 := le_of_lt_succ hum2

    -- max of x,y,z is 2, so each x,y,z can only be 0,1,2.
    -- if m = 0 or 1, x=y=z=0, 3 cannot be u !, contradiction.
    have hm0: m ≠ 0 := by
      rintro meq
      simp only [meq, ge_iff_le, nonpos_iff_eq_zero] at mx my mz
      norm_num [mx, my, mz] at heq
      apply fac_ne heq.symm
    have hm1: m ≠ 1 := by
      rintro meq
      rw [meq, ge_iff_le, ← factorial_eq_one] at mx my mz
      norm_num [mx, my, mz] at heq
      apply fac_ne heq.symm

    -- then m can only be 2
    have meq: m = 2 := by
      omega
    -- u ≥ 3, u ! ≤ 3 x 2 !, we solve u = 3
    have ueq: u = 3 := by
      rw [meq] at uge hum2'
      rw [← factorial_succ] at hum2'
      have: u ≤ 2+1 := by
        by_contra!
        replace: u ≥ 4 := by exact this
        replace: u ! ≥ 4 ! := factorial_le this
        norm_num [factorial_succ] at hum2' this
        linarith only [hum2', this]
      apply le_antisymm this uge

    -- then x! + y! + z! = 6, then x = y = z = 2
    simp only [ueq, and_true, m]
    norm_num [ueq, factorial_succ] at heq
    rw [meq, ge_iff_le] at mx my mz
    clear * - heq mx my mz
    interval_cases x
    all_goals
      interval_cases y
      <;> native_decide +revert

  · -- verify
    rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num [factorial_succ]