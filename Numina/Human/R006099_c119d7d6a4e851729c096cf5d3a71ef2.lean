import Mathlib

-- we show the case when x ≤ y for problem 1
lemma lemma_1 (x y z: ℕ) (l: x ≤ y) (r: 0 < x) (h: Nat.factorial z = Nat.factorial x + Nat.factorial y):
  x = 1 ∧ y = 1 ∧ z = 2 := by
  by_contra! n
  by_cases j: x = y

  -- case x = y
  .
    clear l
    simp [← j] at *
    have u: x < z := by
      by_contra! u
      replace u: Nat.factorial z ≤ Nat.factorial x := by
        apply Nat.factorial_le
        exact u
      simp [h] at u
      absurd u
      apply Nat.factorial_ne_zero
    replace u: x + 1 ≤ z := by omega
    replace u: Nat.factorial (x + 1) ≤ Nat.factorial z := by
      apply Nat.factorial_le
      exact u
    rw [h] at u
    rw [Nat.factorial_succ] at u
    have o:= Nat.factorial_pos x
    replace u: x ≤ 1:= by nlinarith
    have i: x = 1 := by omega
    simp [i] at n h
    have lz: z < 3 := by
      by_contra! lz
      replace lz: Nat.factorial 3 ≤ Nat.factorial z := by
        apply Nat.factorial_le
        exact lz
      rw [h] at lz
      rw [show Nat.factorial 3 = 6 by decide] at lz
      norm_num at lz
    interval_cases z
    .
      simp at h
    .
      simp at h
    .
      simp at n

  -- case x < y
  .
    clear n
    have d: y.factorial ∣ x.factorial := by
      rw [show x.factorial = x.factorial + y.factorial - y.factorial by omega]
      apply Nat.dvd_sub
      omega
      rw [← h]
      apply Nat.factorial_dvd_factorial
      by_contra! s
      replace s: z + 1 ≤ y := by
        omega
      apply Nat.factorial_le at s
      rw [Nat.factorial_succ] at s
      rw [h] at s
      set a:= x.factorial
      set b:= y.factorial
      have ia: 0 < a := by
        apply Nat.factorial_pos
      have ib: 0 < b := by
        apply Nat.factorial_pos
      nlinarith
      simp
    have d2: x.factorial ∣ y.factorial := by
      apply Nat.factorial_dvd_factorial
      exact l
    have v: x.factorial = y.factorial := by
      apply Nat.dvd_antisymm
      exact d2
      exact d
    symm at v
    by_cases k: 1 < y
    .
      rw [Nat.factorial_inj] at v
      simp [v] at j
      exact k
    .
      replace k: y = 1 := by omega
      have i: x = 1 := by omega
      simp [i, k] at j


-- we show the case when x ≤ y ≤ z for problem 2
lemma lemma_2 (x y z w: ℕ) (l1: x ≤ y) (l2: y ≤ z) (r: 0 < x) (h: Nat.factorial w = Nat.factorial x + Nat.factorial y + Nat.factorial z):
  w = 3 ∧ x = 2 ∧ y = 2 ∧ z = 2 := by
    -- we first show that x = y
    have h1: x = y := by
      by_contra! n
      replace l1: x < y := by
        omega
      have c: y.factorial ∣ x.factorial := by
        rw [show x.factorial = x.factorial + y.factorial + z.factorial - (y.factorial + z.factorial) by omega]
        apply Nat.dvd_sub
        omega
        rw [← h]
        apply Nat.factorial_dvd_factorial
        by_contra! s
        replace s: w ≤ y := by
          omega
        apply Nat.factorial_le at s
        rw [h] at s
        have o1: 0 < x.factorial := by
          apply Nat.factorial_pos
        have o2: 0 < z.factorial := by
          apply Nat.factorial_pos
        absurd s
        simp 
        omega
        apply Nat.dvd_add
        simp
        apply Nat.factorial_dvd_factorial
        omega
      have c2: x.factorial ∣ y.factorial := by
        apply Nat.factorial_dvd_factorial
        omega
      have v: x.factorial = y.factorial := by
        apply Nat.dvd_antisymm
        exact c2
        exact c
      rw [← Nat.factorial_lt] at l1
      omega
      omega

    -- then we show that y = z
    simp [h1] at *
    have h2: y = z := by
      by_contra! n
      replace l2: y < z := by
        omega
      have c: z.factorial ∣2 * y.factorial := by
        rw [show 2 * y.factorial = y.factorial + y.factorial + z.factorial - z.factorial by omega]
        apply Nat.dvd_sub
        omega
        rw [← h]
        apply Nat.factorial_dvd_factorial
        by_contra! s
        replace s: w ≤ z := by
          omega
        apply Nat.factorial_le at s
        rw [h] at s
        have o1: 0 < x.factorial := by
          apply Nat.factorial_pos
        have o2: 0 < y.factorial := by
          apply Nat.factorial_pos
        absurd s
        simp 
        omega
        simp
      have c2: (y + 1).factorial ∣ z.factorial := by
        apply Nat.factorial_dvd_factorial
        omega
      have v: (y + 1).factorial ∣ 2 * y.factorial := by
        apply dvd_trans c2 c
      rw [Nat.factorial_succ] at v
      apply Nat.dvd_of_mul_dvd_mul_right at v
      apply Nat.le_of_dvd at v
      have i: y = 1 := by omega
      simp [i] at c
      apply Nat.le_of_dvd at c
      have lz: z < 3 := by 
        by_contra! lz
        replace lz: Nat.factorial 3 ≤ Nat.factorial z := by
          apply Nat.factorial_le
          exact lz
        rw [show Nat.factorial 3 = 6 by decide] at lz
        linarith
      have j: z = 2 := by omega
      simp [i, j] at h
      have lw: w < 3 := by
        by_contra! lw
        replace lw: Nat.factorial 3 ≤ Nat.factorial w := by
          apply Nat.factorial_le
          exact lw
        rw [show Nat.factorial 3 = 6 by decide] at lw
        linarith
      have rw: 2 < w := by
        by_contra! rw
        replace rw: Nat.factorial w ≤ Nat.factorial 2 := by
          apply Nat.factorial_le
          exact rw
        rw [show Nat.factorial 2 = 2 by decide] at rw
        simp [h] at rw
      omega
      norm_num
      norm_num
      apply Nat.factorial_pos

    -- now x = y = z
    simp [h2] at *
    have s: 0 < z.factorial := by
      apply Nat.factorial_pos
    have r1: z < w := by
      by_contra! o
      replace o: Nat.factorial w ≤ Nat.factorial z := by
        apply Nat.factorial_le
        exact o
      rw [h] at o
      omega
    have r2: w ≤ z + 1 := by
      by_contra! o
      have t:= o
      replace o: Nat.factorial (z + 1) ≤ Nat.factorial w := by
        apply Nat.factorial_le
        linarith
      rw [h] at o
      rw [Nat.factorial_succ] at o
      replace o: z ≤ 2 := by
        nlinarith
      interval_cases z
      .
        simp at h
        have lw: w < 3 := by
          by_contra! lw
          replace lw: Nat.factorial 3 ≤ Nat.factorial w := by
            apply Nat.factorial_le
            exact lw
          rw [show Nat.factorial 3 = 6 by decide] at lw
          linarith
        have rw: 2 < w := by
          by_contra! rw
          replace rw: Nat.factorial w ≤ Nat.factorial 2 := by
            apply Nat.factorial_le
            exact rw
          rw [show Nat.factorial 2 = 2 by decide] at rw
          simp [h] at rw
        omega
      .
        simp at h
        have lw: w < 4 := by
          by_contra! lw
          replace lw: Nat.factorial 4 ≤ Nat.factorial w := by
            apply Nat.factorial_le
            exact lw
          rw [show Nat.factorial 4 = 24 by decide] at lw
          linarith
        omega

    -- now w = z + 1
    have v: w = z + 1 := by omega
    simp [v] at *
    rw [Nat.factorial_succ] at h
    have s: 0 < z.factorial := by
      apply Nat.factorial_pos
    replace h: z = 2 := by nlinarith
    simp [h]

  
/-Determine the number of ordered triplets of positive integers
(x,y,z) that satisfy the equation
z!=x!+y!.
Determine the number of ordered quadruples of positive integers
(w,x,y,z) that satisfy the equation
w!=x!+y!+z!.-/

theorem number_theory_612576: {(x, y, z): ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧
    Nat.factorial z = Nat.factorial x + Nat.factorial y}.encard = 1
  ∧ {(w, x, y, z): ℕ × ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < w ∧ Nat.factorial w = Nat.factorial x + Nat.factorial y + Nat.factorial z}.encard = 1 := by
 
    constructor

    -- the first part of the problem
    .
      have h_eq: {(x, y, z): ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ Nat.factorial z = Nat.factorial x + Nat.factorial y} = {(1, 1, 2)} := by
        ext ⟨x, y, z⟩
        constructor

        -- the forward direction
        .
          intro h
          simp at h
          rcases h with ⟨hx, hy, hz, h⟩
          by_cases l: x ≤ y
          .
            simp
            apply lemma_1 x y z l (by omega) h  -- apply lemma_1
          .
            replace l: y ≤ x := by omega
            rw [show Nat.factorial x + Nat.factorial y = Nat.factorial y + Nat.factorial x by omega] at h
            have f:= lemma_1 y x z l (by omega) h  --apply lemma_1
            simp
            omega

        -- the backward direction
        .
          intro h
          simp at h
          simp [h]

      -- count the card
      rw [h_eq]
      simp [Set.encard_singleton]


    -- the second part of the problem
    .
      have h_eq: {(w, x, y, z): ℕ × ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < w ∧
        Nat.factorial w = Nat.factorial x + Nat.factorial y + Nat.factorial z}
        = {(3, 2, 2, 2)} := by
        ext ⟨w, x, y, z⟩
        constructor

        -- the forward direction
        .
          intro h
          simp at h
          rcases h with ⟨hx, hy, hz, hw, h⟩
          simp


          -- we check all orders of x, y, z using lemma_2
          have u: (x ≤ y ∧ y ≤ z) ∨ (x ≤ z ∧ z ≤ y) ∨ (y ≤ x ∧ x ≤ z) ∨ (y ≤ z ∧ z ≤ x) ∨
            (z ≤ x ∧ x ≤ y) ∨ (z ≤ y ∧ y ≤ x) := by
            omega
          rcases u with u | u | u | u | u | u

          -- case x ≤ y ∧ y ≤ z
          .
            apply lemma_2 x y z w (by omega) (by omega) (by omega) h

          -- case x ≤ z ∧ z ≤ y
          .
            rw [show Nat.factorial x + Nat.factorial y + Nat.factorial z =
              Nat.factorial x + Nat.factorial z + Nat.factorial y by omega] at h
            have i:= lemma_2 x z y w (by omega) (by omega) (by omega) h
            omega

          -- case y ≤ x ∧ x ≤ z
          .
            rw [show Nat.factorial x + Nat.factorial y + Nat.factorial z =
              Nat.factorial y + Nat.factorial x + Nat.factorial z by omega] at h
            have i:= lemma_2 y x z w (by omega) (by omega) (by omega) h
            omega

          -- case y ≤ z ∧ z ≤ x
          .
            rw [show Nat.factorial x + Nat.factorial y + Nat.factorial z =
              Nat.factorial y + Nat.factorial z + Nat.factorial x by omega] at h
            have i:= lemma_2 y z x w (by omega) (by omega) (by omega) h
            omega

          -- case z ≤ x ∧ x ≤ y
          .
            rw [show Nat.factorial x + Nat.factorial y + Nat.factorial z =
              Nat.factorial z + Nat.factorial x + Nat.factorial y by omega] at h
            have i:= lemma_2 z x y w (by omega) (by omega) (by omega) h
            omega

          -- case z ≤ y ∧ y ≤ x
          .
            rw [show Nat.factorial x + Nat.factorial y + Nat.factorial z =
              Nat.factorial z + Nat.factorial y + Nat.factorial x by omega] at h
            have i:= lemma_2 z y x w (by omega) (by omega) (by omega) h
            omega

        -- the backward direction
        .
          intro h
          simp at h
          simp [h]
          decide

      -- count the card
      rw [h_eq]
      simp [Set.encard_singleton]