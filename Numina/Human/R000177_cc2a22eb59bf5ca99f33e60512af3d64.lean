import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 400000

/- Let  $p,q$  be prime numbers $.$  Prove that if  $p+q^2$  is a perfect square,
    then  $p^2+q^n$  is not a perfect square for any positive integer  $n.$-/
theorem number_theory_8494
  (p q : ℕ)
  (h₀ : p.Prime ∧ q.Prime)
  (h₁ : ∃ m, m^2 = p + q^2) :
  ∀ n > 0, ¬ ∃ m, m^2 = p^2 + q^n := by
    -- To prove that \( p^2 + q^n \) is not a perfect square for any positive integer \( n \),
    -- given that \( p + q^2 \) is a perfect square and \( p \) and \( q \) are prime numbers,
    -- follow these steps:
    intro n hn hcont
  --   Given \( p + q^2 = a^2 \) for some integer \( a \), we can rewrite this as:
  --  \[
  --  p = a^2 - q^2 = (a - q)(a + q)
  --  \]
    obtain ⟨a, ha⟩ := h₁
    replace ha : p = a^2 - q^2 := Nat.eq_sub_of_add_eq ha.symm
    have c1 : p = (a - q) * (a + q) := by rw [ha, Nat.sq_sub_sq]; ring
  --  Since \( p \) is prime, the factors must satisfy either \( a - q = 1 \) and \( a + q = p \), leading to:
  --  \[
  --  a = q + 1 \quad \text{and} \quad p = 2q + 1
  --  \]
    have c2 : p = 2 * q + 1 := by
      have := Nat.prime_mul_iff.1 (c1 ▸ h₀.1)
      rcases this with hl | hr
      · rcases Nat.add_eq_one_iff.1 hl.2 with h1 | h2
        · simp [h1] at hl
          exfalso; exact Nat.not_prime_zero hl
        · simp [h2] at hl
          exfalso; exact Nat.not_prime_one hl
      · have c2 : a = q + 1 := by omega
        simp [c2] at c1
        rw [c1]
        linarith
  --  Assume \( p^2 + q^n = b^2 \) and analyze the equation:
  --  \[
  --  b^2 = 4q^2 + 4q + 1 + q^n
  --  \]
  --  This can be rearranged as:
  --  \[
  --  b^2 - p^2 = q^n
  --  \]
    obtain ⟨b, hb⟩ := hcont
    have c3 : q^n = (b - p) * (b + p) := by
      have : q^n = b^2 - p^2 := by omega
      simp [this, Nat.sq_sub_sq]
      ring
    have hpb : p < b := by
      by_contra! tmp
      simp [tmp] at c3
      exact Nat.not_prime_zero (c3.1 ▸ h₀.2)
    -- Since $q ^ n = (b - p) * (b + p)$, we have there exists $i, j$ such that
    -- $b - p = q ^ i$ and $b + p = q ^ j$.
    obtain ⟨i, hi⟩ := (Nat.dvd_prime_pow (h₀.2)).1 (Dvd.intro (b + p) c3.symm)
    obtain ⟨j, hj⟩ := (Nat.dvd_prime_pow (h₀.2)).1 (Dvd.intro_left (b - p) c3.symm)
    have h0 : i < j := by
      have : b - p < b + p := by omega
      simp [hi, hj] at this
      exact (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt h₀.2)).1 this
    -- Since $b - p$ and $b + p$ are both powers of $q$, so the gcd of them is also power of $q$.
    have h1 :  (b - p).gcd (b + p) = q^i := by
      simp [hi, hj]
      rw [Nat.gcd_eq_iff]
      simp
      exact ⟨Nat.pow_dvd_pow q (le_of_lt h0), by tauto⟩
    -- Simplifying, we get $q^i \mid 4 * q + 2$.
    have h2 : q^i ∣ 4 * q + 2 := by
      have : (b - p).gcd (b + p) ∣ 2 * p := by
        convert Nat.dvd_sub (by omega) (Nat.gcd_dvd_right (b-p) (b+p)) (Nat.gcd_dvd_left (b-p) (b+p))  using 1
        apply Nat.eq_sub_of_add_eq
        rw [←Nat.add_sub_assoc (le_of_lt hpb)]
        omega
      rw [h1, c2] at this
      convert this using 1
      linarith
    -- But we have both  $b - p$  and  $b + p$  to be the power of  $q$ . So, we must have
    -- either  $b - p = 1$  or  $q = 2$ .
    have h3 : b = p + 1 ∨ q = 2 := by
      by_cases r0 : i = 0
      · simp [r0] at hi
        exact Or.inl (by omega)
      · by_cases q2 : q = 2
        · tauto
        · have oddq : Odd q := Nat.Prime.odd_of_ne_two h₀.2 q2
          have h3 : q^i ∣ 2 * q + 1 := by
            rw [show 4 * q + 2 = (2 * q + 1) * 2 by linarith] at h2
            exact (Nat.Coprime.dvd_mul_right (Coprime.pow_left i (Nat.coprime_two_right.2 oddq))).1 h2
          have ine1 : i ≠ 1 := by
            intro i1
            simp [i1] at h3
            have : q ∣ 1 := by
              convert Nat.dvd_sub (show 2*q ≤ 2*q + 1 by omega) h3 (Nat.dvd_mul_left q 2)
              omega
            have : 1 < q ∧ q ≤ 1 := ⟨Nat.Prime.one_lt h₀.2, Nat.le_of_dvd (by omega) this⟩
            linarith
          have h4 : 3 ≤ q → 2 * q + 1 < q^2 := by
            intro h
            nlinarith
          have qge3 : 3 ≤ q := by
            have : 2 ≤ q := Nat.Prime.two_le h₀.2
            omega
          have : 2 * q + 1 < q ^ i := lt_of_lt_of_le (h4 qge3)
            (Nat.pow_le_pow_of_le (Nat.Prime.one_lt h₀.2) (by omega))
          have := Nat.le_of_dvd (by omega) h3
          linarith
    have o3 := c3
    rcases h3 with hl | hr
    · -- Case 1 : $b = p + 1$ : If  $b - p = 1$ , then $q^n = (p + 1)^2 - p^2 = 2p + 1 = 4q + 3$ .
      -- It is easy to prove that  $n$  has to be odd and  $q^n \ge 4q + 3$  for  $q,n \ge 3$ .
      -- This contradicts with $q ^ n = 4 * q + 3$.
      simp [hl, c2] at c3
      replace c3 : q^n = 4 * q + 3 := by linarith
      have oddq : Odd q := by
        by_contra! evenq
        simp at evenq
        have evenqn : Even (q^n) := (even_pow' (by omega)).mpr evenq
        have oddqn : Odd (q^n) := c3 ▸ ⟨2 * q + 1, by linarith⟩
        exact Nat.not_even_iff_odd.2 oddqn evenqn
      have qge3 : 3 ≤ q := by
        have : 2 ≤ q := Nat.Prime.two_le h₀.2
        have : 2 ≠ q := fun h => (by have := h ▸ oddq; tauto)
        omega
      have nge3 : 3 ≤ n := by
        by_contra!
        interval_cases n
        · linarith
        · have qlt5 : q < 5 := by
            by_contra! qge5
            have c4 : 4 * q + 3 < q^2 := calc
              _ < 5 * q := by linarith
              _ ≤ _ := by nlinarith
            simp [c3] at c4
          interval_cases q <;> simp at c3
      have : 4 * q + 3 < q^n := calc
        _ ≤ 5 * q := by linarith
        _ < q^2 * q := by nlinarith
        _ ≤ _ := by
          nth_rw 2 [←pow_one q]
          rw [←pow_add q]
          refine pow_le_pow_of_le_right (by positivity) nge3
      simp [c3] at this
    · -- Case 2 : $q = 2$ : If  $q = 2$ , then we must have  $p = 5$ , $2^n = (b - 5)(b + 5)$ .
      simp [hr] at c2
      simp [hr, c2] at c3 hi hj hpb
      have h3 : i = 1 ∨ i = 0 := by
        have : 2^j - 2^i = 10 := by
          rw [←hi.2, ←hj.2]
          apply Nat.sub_eq_of_eq_add
          rw [←Nat.add_sub_assoc (le_of_lt hpb)]
          omega
        have : 2^i * (2^(j-i) - 1) = 10 := by
          rw [Nat.mul_sub, ←pow_add, ←Nat.add_sub_assoc (le_of_lt h0), Nat.add_sub_cancel_left]
          simpa
        have : 2^i ∣ 10 := Dvd.intro (2 ^ (j - i) - 1) this
        have : i < 4 := by
          have := Nat.le_of_dvd (by omega) this
          have : 2 ^ i < 2 ^ 4 := by nlinarith
          exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
        interval_cases i <;> tauto
      rw [hi.2] at c3
      simp [hr, c2] at o3
      -- If  $b - 5 = 1$ , then it clearly doesn't satisfy. So, we must have  $b - 5 = 2$ , which dont satisfy as well.
      -- In either case, we're finished.
      rcases h3 with h3 | h3 <;> simp [h3] at hi
      · have : b = 7 := by omega
        simp [this] at o3
        have : n < 5 := by
          have : 2^n < 2^ 5 := by linarith
          exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
        interval_cases n <;> simp at o3
      · have : b = 6 := by omega
        simp [this] at o3
        have : n < 4 := by
          have : 2^n < 16 := by omega
          exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
        interval_cases n <;> simp at o3
