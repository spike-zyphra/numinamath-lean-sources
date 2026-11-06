import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Prove that the positive integers  $n$  that cannot be written as a sum of
  $r$  consecutive positive integers, with  $r>1$ , are of the form  $n=2^l~$  for some
  $l\geqslant 0$ .-/
theorem number_theory_8868
  (n : ℕ)
  (hn : ∃ r m, 1 < r ∧ 0 < m ∧ ∑ i in Finset.range r, (m + i) = n) :
    ¬∃ l, n = 2^l := by
      -- an auxiliary lemma : 2 divides products of two consecutive natural numbers
      have aux (n : ℕ) : 2 ∣ n * (n + 1) := by
        by_cases h : n % 2 = 0
        · replace h :=  Nat.dvd_of_mod_eq_zero h
          exact Dvd.dvd.mul_right h (n + 1)
        · have : n % 2 < 2 := Nat.mod_lt n (by linarith)
          have h : n % 2 = 1 := by simp at *; linarith
          have : (n + 1) % 2 = 0 := by rw [Nat.add_mod]; simp [h]
          have := Nat.dvd_of_mod_eq_zero this
          exact Dvd.dvd.mul_left this n
      intro h
      obtain ⟨l, hl⟩ := h
      obtain ⟨r, m, hr, hm, c1⟩ := hn
      replace c1 : n = r * m + r * (r - 1) / 2 := by
        rw [←c1, Finset.sum_add_distrib]
        simp
        exact Finset.sum_range_id r
      rw [hl] at c1
      -- According ,to our assumption we can say that
      -- $n=rm +\frac{r(r-1)}{2}= 2^{\ell}$ . $\implies 2^{\ell+1} = r(2m-1+r)$ .
      replace c1 : 2^(l + 1) = 2 * r * m + r * (r - 1) := by
        rw [pow_add, pow_one, c1, add_mul, Nat.div_mul_cancel]
        nlinarith
        convert aux (r - 1) using 1
        rw [Nat.sub_add_cancel (le_of_lt hr)]
        ring
      replace c1 : 2^(l + 1) = r * (2 * m - 1 + r) := by
        rw [mul_add, Nat.mul_sub]
        rw [Nat.mul_sub] at c1
        ring_nf at c1 ⊢
        rw [c1]
        zify
        rw [Nat.cast_sub (by nlinarith), Nat.cast_sub (by nlinarith)]
        simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
        linarith
      rcases Nat.even_or_odd r with evenr | oddr
      · -- Case 1 : $r$ is even.
        -- We can see that  $2m-1 + r$  is an odd integer.
        have h1 : Odd (2 * m - 1 + r ) := by
          refine odd_add.mpr ?_
          simp [evenr]
          refine (odd_sub' (by linarith)).mpr ?_
          simp
        -- we can see that $2m -1 + r \mid 2^{l+1}$.
        have h2 : (2 * m - 1 + r ) ∣ 2^(l + 1):= ⟨r, by linarith⟩
        obtain ⟨k, _, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
        have _ := hk2 ▸ h1
        have k0 : k = 0 := by
          by_contra!
          have : 2 ∣ 2 ^ k := by exact dvd_pow_self 2 this
          have : Even (2 ^ k) := (even_iff_exists_two_nsmul (2 ^ k)).mpr this
          have := hk2 ▸ this
          exact Nat.not_odd_iff_even.2 this h1
        -- Which is clearly a contradiction !!!!!!!!!!!!
        simp [k0] at hk2
        linarith
      · -- Case 2 : $r$ is odd.
        have h1 : r ∣ 2^(l + 1) := ⟨2 * m - 1 + r, c1⟩
        obtain ⟨k, _, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
        have := hk2 ▸ oddr
        have k0 : k = 0 := by
          by_contra!
          have : 2 ∣ 2 ^ k := by exact dvd_pow_self 2 this
          have : Even (2 ^ k) := (even_iff_exists_two_nsmul (2 ^ k)).mpr this
          have := hk2 ▸ this
          exact Nat.not_odd_iff_even.2 this oddr
        -- Clearly like previous it is not possible if $r>1$ only possibility  $\boxed{r=1}$ .
        -- Contradiction!!!!!!! It complete our proof.
        simp [k0] at hk2
        linarith
