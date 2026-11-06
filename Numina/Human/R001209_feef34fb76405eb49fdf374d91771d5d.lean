import Mathlib

/- The two positive integer solutions of the equation $x^2 - mx + n = 0$ are $k$ and $t$, where $m$ and $n$ are both prime numbers and $k > t$. What is the value of $m^n + n^m + k^t + t^k$? -/
theorem algebra_21364 {m n k t : ℕ} (hm : m.Prime) (hn : n.Prime)
    (hroots : (k : ℤ)^2 - m * k + n = 0 ∧ (t : ℤ)^2 - m * t + n = 0) (hk : k > t) :
    m^n + n^m + k^t + t^k = 20 := by
  -- $k - t \neq 0$
  have ksubtne : (k : ℤ) - t ≠ 0 := by  
    have knet : k ≠ t := by
      exact Ne.symm (Nat.ne_of_lt hk)
    apply (Mathlib.Tactic.Zify.natCast_ne k t).mp at knet
    exact sub_ne_zero_of_ne knet
  -- $k + t = m$
  have eq : (k : ℤ)^2 - m * k + n - (t^2 - m * t + n) = (k - t) * (k + t - m) := by
    ring
  rw [hroots.1, hroots.2] at eq
  simp only [sub_self, zero_eq_mul, ksubtne, false_or] at eq
  have meq : k + t = m := by
    linarith
  -- $k * t = n$
  have neq : k * t = n := by
    nlinarith
  -- t = 1$
  have teq : t = 1 := by  
    have teq : t = 1 ∨ t = n := by
      refine (Nat.dvd_prime hn).mp ?_
      exact Dvd.intro_left k neq
    rcases teq with teq | teq
    exact teq
    have ngt : 0 < n := by
      exact Nat.Prime.pos hn
    have keq : k = 1 := by
      nlinarith
    linarith
  -- $k = n$
  have keq : k = n := by
    nlinarith
  rw [keq, teq]
  rw [keq, teq] at meq
  -- $m$ is odd
  have modd : Odd m := by
    have mne : m ≠ 2 := by
      nlinarith
    exact Nat.Prime.odd_of_ne_two hm mne
  -- $n$ is even, so $n = 2$
  have neven : Even n := by
    have mneven : ¬Even m := by
      exact Nat.not_even_iff_odd.mpr modd
    apply Nat.even_add_one.mpr at mneven
    rw [meq.symm] at mneven
    refine even_iff_two_dvd.mpr ?_
    apply even_iff_two_dvd.mp at mneven
    exact Nat.dvd_add_self_right.mp mneven
  have neq2 : n = 2 := by
    exact (Nat.Prime.even_iff hn).mp neven
  -- so the result is $20$
  rw [meq.symm, neq2]
  norm_num