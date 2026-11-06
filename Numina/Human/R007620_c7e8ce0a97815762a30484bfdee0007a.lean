import Mathlib
/- The Fibonacci sequence is defined by $F_1 = F_2 = 1$ and $F_n = F_{n - 1} + F_{n - 2}$ for $n \ge 3.$

Compute
\[\sum_{j = 1}^{2004} i^{2004 - F_j}.\] -/

theorem algebra_20801 : ∑ j in (Finset.Ioc 0 2004), (.I : ℂ)^(2004  - (Nat.fib j :ℤ)) = -668 * .I := by

  -- prove that i^{2004 - n} equals to i^{-n}
  have simp_pow (n: ℤ) : (.I : ℂ)^(2004  - n) = (.I : ℂ)^(- n) := by {
    have mul_4 : (2004 : ℤ)  = 501 * (4:ℕ) := by simp
    rw [
      -- we need to convert the integer to a complex number, and then convert it back
      mul_4,
      Int.sub_eq_add_neg,
      <- Complex.cpow_intCast,
      Int.cast_add,
      Complex.cpow_add,
      Int.cast_mul,
      Complex.cpow_int_mul,
    ]
    nth_rw 2 [Complex.cpow_intCast]
    simp
    simp
  }

  -- i^{F_n} is periodic
  -- define the periodic function
  let i_pow_fib' := fun j => match j % 6 with
    | 0 => 1
    | 1 => -Complex.I
    | 2 => -Complex.I
    | 3 => -1
    | 4 => Complex.I
    | 5 => -Complex.I
    | _ => 0

  -- prove that i^{F_n} equals to the periodic function
  -- use the second induction principle
  let motive (n: ℕ) := Complex.I ^ (- (Nat.fib n :ℤ)) = i_pow_fib' n
  have rec_ind: (n: ℕ) → ((m : Nat) → m < n → motive m) → motive n := by
    simp only [motive]
    intro n ih
    match n with
    | 0 => {
      unfold Nat.fib
      simp
    }
    | 1 => {
      unfold Nat.fib
      simp
    }
    | n + 2 => {
      rw [Nat.fib_add_two]
      rw [
        <- Complex.cpow_intCast,
        Int.cast_neg,
        Nat.cast_add,
        Int.cast_add,
        neg_add,
        Complex.cpow_add,
        <-Int.cast_neg,
        <-Int.cast_neg,
        Complex.cpow_intCast,
        Complex.cpow_intCast,
      ]
      have ihm1: (Complex.I ^ (- (Nat.fib (n + 1):ℤ))) = i_pow_fib' (n+1) := ih (n+1) (by linarith)
      have ihm2: (Complex.I ^ (- (Nat.fib (n):ℤ))) = i_pow_fib' n := ih n (by linarith)
      rw [ihm1, ihm2]
      simp only [i_pow_fib']
      -- it is ugly to prove the periodicity of i^{F_n} by case analysis
      match n_mod_6: n % 6 with
      | 0 => {
        have n_1_mod: (n + 1) % 6 = 1 := by rw [<- Nat.mod_add_mod, n_mod_6];
        have n_2_mod: (n + 2) % 6 = 2 := by rw [<- Nat.mod_add_mod, n_mod_6];
        rw [n_1_mod, n_2_mod]
        simp
      }
      | 1 => {
        have n_1_mod: (n + 1) % 6 = 2 := by rw [<- Nat.mod_add_mod, n_mod_6];
        have n_2_mod: (n + 2) % 6 = 3 := by rw [<- Nat.mod_add_mod, n_mod_6];
        rw [n_1_mod, n_2_mod]
        simp
      }
      | 2 => {
        have n_1_mod: (n + 1) % 6 = 3 := by rw [<- Nat.mod_add_mod, n_mod_6];
        have n_2_mod: (n + 2) % 6 = 4 := by rw [<- Nat.mod_add_mod, n_mod_6];
        rw [n_1_mod, n_2_mod]
        simp
      }
      | 3 => {
        have n_1_mod: (n + 1) % 6 = 4 := by rw [<- Nat.mod_add_mod, n_mod_6];
        have n_2_mod: (n + 2) % 6 = 5 := by rw [<- Nat.mod_add_mod, n_mod_6];
        rw [n_1_mod, n_2_mod]
        simp
      }
      | 4 => {
        have n_1_mod: (n + 1) % 6 = 5 := by rw [<- Nat.mod_add_mod, n_mod_6];
        have n_2_mod: (n + 2) % 6 = 0 := by rw [<- Nat.mod_add_mod, n_mod_6];
        rw [n_1_mod, n_2_mod]
        simp
      }
      | 5 => {
        have n_1_mod: (n + 1) % 6 = 0 := by rw [<- Nat.mod_add_mod, n_mod_6];
        have n_2_mod: (n + 2) % 6 = 1 := by rw [<- Nat.mod_add_mod, n_mod_6];
        rw [n_1_mod, n_2_mod]
        simp
      }
      | n' + 6 => {
        exfalso
        have lt_six: n % 6 < 6 := Nat.mod_lt n (by norm_num)
        rw [n_mod_6] at lt_six
        linarith
      }
      simp
    }

  -- replace the function with the periodic function
  have simp_fun: (fun j => Complex.I ^ (2004 - (Nat.fib j: ℤ))) = i_pow_fib' := by
    funext x
    rw [simp_pow]
    exact Nat.strongRec rec_ind x
  rw [simp_fun]

  -- calculate the sum of one period
  have sum_ioc_6 (n:ℕ): (Finset.Ioc (6*n) (6*(n+1))).sum i_pow_fib' = -2 * Complex.I := by
    rw [Nat.Ioc_eq_range']
    have exp: 6*(n+1) = 6 * n + 6 := by ring_nf
    rw [exp]
    simp
    repeat (unfold List.range')
    simp
    ring_nf
    simp [i_pow_fib']
    ring_nf

  -- calculate the sum of the whole sequence
  have sum_ind (n:ℕ): (Finset.Ioc 0 (6*n)).sum i_pow_fib' = -2*n*Complex.I := by
    induction n with
    | zero => simp
    | succ n ih => {
      have sum_6: (Finset.Ioc (6*n) (6*(n+1))).sum i_pow_fib' = -2 * Complex.I := sum_ioc_6 n

      have le1: 0 ≤ 6*n := by linarith
      have le2: 6 * n ≤ 6*(n + 1) := by linarith
      have disjoint: Disjoint (Finset.Ioc 0 (6 * n)) (Finset.Ioc (6 * n) (6 * (n + 1))) :=
        Finset.disjoint_left.2 fun _ hab hbc => (Finset.mem_Ioc.mp hab).2.not_lt (Finset.mem_Ioc.mp hbc).1
      rw [<- (Finset.Ioc_union_Ioc_eq_Ioc le1 le2), (Finset.sum_union disjoint)]
      rw [ih, sum_6, <- sub_eq_zero]
      calc -2 * ↑n * Complex.I + -2 * Complex.I - -2 * ↑(n + 1) * Complex.I = (-2 * ↑n + -2 - -2 * ↑(n + 1)) * Complex.I := by ring_nf
      _ =(-2 * ↑n + -2 - -2 * (↑n + 1)) * Complex.I := by simp
      _ =(-2 * ↑n + -2 + 2 * ↑n + 2) * Complex.I := by ring_nf
      _ = 0 := by ring_nf

    }

  -- calculate the sum of the whole sequence
  have sum_2004: (Finset.Ioc 0 2004).sum i_pow_fib' = -2*334*Complex.I := sum_ind 334
  rw [sum_2004]
  ring_nf
