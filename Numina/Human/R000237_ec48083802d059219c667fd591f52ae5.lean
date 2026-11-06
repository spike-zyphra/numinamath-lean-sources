import Mathlib

/- A natual number is composite if it is greater than or equal 2 and not prime. -/
def composite (n : ℕ) : Prop :=
  2 ≤ n ∧ ¬n.Prime

/- Given that  $n$  and  $r$  are positive integers.
Suppose that
\[ 1 + 2 + \dots + (n - 1) = (n + 1) + (n + 2) + \dots + (n + r) \]
Prove that  $n$  is a composite number.-/
theorem number_theory_8659 {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hnr : ∑ i in Finset.Icc 1 (n - 1), i = ∑ i in Finset.Icc (n + 1) (n + r), i) :
    composite n := by
  rcases le_or_lt n 1 with hn | hn
  -- If n = 1, it is easy to check that LHS < RHS as LHS = 0 and RHS > 0.
  . interval_cases n
    norm_num at hnr
    rw [add_comm, show Finset.Icc 2 (r + 1) = Finset.Ico 2 (r + 1 + 1) from rfl,
      Finset.sum_Ico_eq_sum_range, show r + 1 + 1 - 2 = r - 1 + 1 by omega,
      Finset.sum_range_succ, add_comm, eq_comm] at hnr
    have := Nat.le.intro hnr
    omega
  constructor
  . exact hn
  intro hnp
  apply_fun (· * 2) at hnr
  -- It is easy to calculate LHS : $$ \frac{(p)(p-1)}{2} $$.
  have lhs : (∑ i ∈ Finset.Icc 1 (n - 1), i) * 2 = n * (n - 1) := calc
    _ = (∑ i ∈ Finset.Icc 0 (n - 1), i) * 2 := by
      nth_rw 2 [← Finset.sum_Ioc_add_eq_sum_Icc (by omega)]
      rw [add_zero, show Finset.Ioc 0 (n - 1) = Finset.Icc 1 (n - 1) from rfl]
    _ = _ := by
      rw [show Finset.Icc 0 (n - 1) = Finset.Ico 0 (n - 1 + 1) from rfl,
        Finset.sum_Ico_eq_sum_range, show n - 1 + 1 - 0 = n by omega,
        ← Finset.sum_range_id_mul_two]
      simp
  -- While the RHS is equal to   $$ \frac{(2p+r+1)(r)}{2} $$ .
  have rhs : (∑ i ∈ Finset.Icc (n + 1) (n + r), i) * 2 = (2 * n + r + 1) * r := by
    have : ∑ i ∈ Finset.Icc (n + 1) (n + r), i = ∑ x ∈ Finset.range r, (n + 1 + x) := by
      rw [show Finset.Icc (n + 1) (n + r) = Finset.Ico (n + 1) (n + r + 1) from rfl,
        Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr
      . simp
      intros
      ac_rfl
    rw [this]
    have := Finset.sum_range_add (fun i => i) (n + 1) r
    apply_fun (· * 2) at this
    rw [add_mul, Finset.sum_range_id_mul_two, Finset.sum_range_id_mul_two] at this
    zify at this ⊢
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at this
    push_cast at this
    linear_combination -this
  rw [lhs, rhs] at hnr
  -- Also, since  $p$  is prime, it must divide on of the 2 factors on the RHS
  have hndvd : n ∣ (2 * n + r + 1) * r := by use n - 1; exact hnr.symm
  rw [Nat.Prime.dvd_mul hnp] at hndvd
  -- However,  $p-1>r$ , so  $p$  cannot divide  $r$ Hence,
  -- $p$  must divide  $2p+r+1$ ,
  replace hndvd : n ∣ 2 * n + r + 1 := by
    rcases hndvd with h | h
    . trivial
    have := Nat.le_of_dvd hr h
    have : n - 1 < 2 * n + r + 1 := by omega
    have : n * (n - 1) < r * (2 * n + r + 1) := by nlinarith
    linarith
  -- implying that  $p|r+1$
  -- Since  $r$  is a positive integer, this implies that  $r$  must be at least  $p-1$ .
  replace hndvd : n ∣ r + 1 := by
    zify at hndvd ⊢
    have := hndvd.sub ((Int.dvd_refl n).mul_left 2)
    ring_nf at this
    convert this using 1
    ac_rfl
  -- But this would clearly make the RHS larger than the LHS in the original equation.
  have := Nat.le_of_dvd (by positivity) hndvd
  have : n - 1 ≤ r := by omega
  have : n < 2 * n + r + 1 := by omega
  have : n * (n - 1) < (2 * n + r + 1) * r := by nlinarith
  linarith
