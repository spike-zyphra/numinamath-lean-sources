import Mathlib

open Nat

def a : ℕ → ℕ
| 0 => 2
| 1 => 1
| n + 2 => a n + a (n + 1)

theorem number_theory_641855 (k p : ℕ) (hp : Nat.Prime p) (hpk : p ∣ a (2 * k) + 2) :
  p ∣ a (2 * k + 1) + 1 := by 
  -- first prove that a n = fib (n + 1) + fib (n - 1)
  have h1 : ∀ n, n ≥ 1 → a n = fib (n + 1) + fib (n - 1) := by 
    have h1' : ∀ n, n ≥ 1 → a n = fib (n + 1) + fib (n - 1) ∧ a (n + 1) =  fib (n + 2) + fib n := by
      intro n hn 
      induction' hn with m ih1 ih2
      · simp
        constructor
        · rfl
        · unfold a
          rfl
      · simp
        simp at ih1
        have aux1 : a (m + 1) = a m + a (m - 1) := by 
          have aux2 : (m + 1) = m - 1 + 2 := by omega
          rw [aux2]
          conv => 
            lhs
            unfold a
          rw [show m - 1 + 1 = m by omega]
          ring
        obtain ⟨ih2, ih3⟩ := ih2
        constructor
        · rw [ih3]
        · conv => 
            unfold a
          rw [ih2, ih3]
          have aux2 : fib (m + 1 + 2) = fib (m + 2) + fib (m + 1) := by 
            rw [fib_add_two]
            ring
          rw [aux2]
          have aux3 : fib (m + 1) = fib m + fib (m -1) := by 
            have aux2 : (m + 1) = m - 1 + 2 := by omega
            rw [aux2,fib_add_two, show m - 1 + 1 = m by omega]
            ring
          nth_rw 3 [aux3]
          ring
    intro n hn
    exact (h1' n hn).1
  -- the second equation, fib (n - 1) * fib (n + 1) - (fib n : ℤ) ^ 2 = (-1) ^ n 
  have h2 : ∀ n, n ≥ 1 → fib (n - 1) * fib (n + 1) - (fib n : ℤ) ^ 2 = (-1) ^ n := by
    intro n hn
    induction' hn with m ih1 ih2
    · simp
    · simp
      simp at ih1
      rw [fib_add_two]
      have aux1 : ((fib (m + 1)) : ℤ) ^ 2 = fib (m + 1) * (fib m + fib (m - 1)) := by 
        have aux2 : fib (m + 1) = fib m + fib (m - 1) := by 
          rw [show m + 1 = m - 1 + 2 by omega, fib_add_two, show m - 1 + 1 = m by omega]
          ring
        zify at aux2
        rw [←aux2]
        ring
      rw [aux1, pow_add, ←ih2]
      simp
      ring
  -- prove the third equation, ∀ n, a (2 * n) = a n ^ 2 - 2 * (-1 : ℤ) ^ n 
  have h3 : ∀ n, a (2 * n) = a n ^ 2 - 2 * (-1 : ℤ) ^ n := by 
    intro n
    by_cases hn0 : n = 0
    · rw [hn0]
      simp
      rfl
    · have nge1 : n ≥ 1 := by 
        omega
      have nge : 2 * n ≥ 1 := by 
        linarith
      rw [h1 (2 * n) nge, h1 n nge1]
      norm_num
      have aux1 : fib (2 * n - 1) = fib n ^ 2 + fib (n - 1) ^ 2 := by 
        have aux2 : 2 * n - 1 = 2 * (n - 1) + 1 := by 
          omega
        rw [aux2, fib_two_mul_add_one, show n - 1 + 1 = n by omega]
      rw [fib_two_mul_add_one, aux1, ←h2 n nge1]
      simp
      ring
  -- prove the fourth equation, ∀ n, a (2 * n) = 5 * fib n ^ 2 + 2 * (- 1 : ℤ) ^ n
  have h4 : ∀ n, a (2 * n) = 5 * fib n ^ 2 + 2 * (- 1 : ℤ) ^ n := by 
    intro n
    by_cases hn0 : n = 0 
    · rw [hn0]
      simp
      rfl
    · have nge : n ≥ 1 := by 
        omega
      rw [h3, h1 n nge]
      simp
      have aux1 : (fib n : ℤ) = fib (n + 1) - fib (n - 1) := by 
        rw [show n + 1 = n - 1 + 2 by omega, fib_add_two, show n - 1 + 1 = n by omega]
        simp
      calc 
        _ = 4 * (fib n : ℤ) ^ 2 + (fib n : ℤ) ^ 2 + 2 * (-1) ^ n := by 
          nth_rw 2 [aux1]
          rw [←h2 n nge]
          ring
        _ = _ := by 
          ring
  -- prove the fifth equation, ∀ n, a (2 * n + 1) = a n * a (n + 1) - (- 1 : ℤ) ^ n 
  have h5 : ∀ n, a (2 * n + 1) = a n * a (n + 1) - (- 1 : ℤ) ^ n := by 
    intro n
    induction n with 
    | zero => 
      simp
      rfl
    | succ m ih => 
      have aux1 : (a (2 * (m + 1) + 1)) = a (2 * (m + 1)) + a (2 * m + 1) := by
        conv => 
          lhs 
          rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]
          unfold a
        ring_nf
      simp [aux1, ih, h3, pow_add]
      have aux2 : a (m + 1 + 1) = a (m + 1) + a m := by 
        conv => 
          lhs
          rw [show m + 1 + 1 = m + 2 by ring]
          unfold a
        ring
      simp [aux2]
      ring_nf
  -- now we prove all the identity we need, next we prove our goal, discuss by_cases k is odd or even, the even cases is easier than the odd case
  by_cases heven : Even k
  -- the case k is even
  · zify at hpk ⊢ 
    rw [h3] at hpk
    have aux : (-1) ^ k = 1 := by
      exact Even.neg_one_pow heven
    simp [aux] at hpk
    have pdvd : p ∣ a k := by 
      norm_cast at hpk
      exact Nat.Prime.dvd_of_dvd_pow hp hpk
    simp [h5, aux]
    norm_cast
    exact Dvd.dvd.mul_right pdvd (a (k + 1))
  -- the case k is odd
  · have hodd : Odd k := by 
      simp at heven
      exact heven
    zify at hpk ⊢
    have hpk' : (p : ℤ) ∣ ↑(a (2 * k)) + 2 := hpk
    rw [h4] at hpk
    have aux : (-1) ^ k = - 1 := by   
      exact Odd.neg_one_pow hodd
    simp [aux] at hpk
    -- now discuss by cases whether p is 5 or not
    by_cases peq5 : p = 5
    -- the case p = 5
    · 
      have aux1 : ∀ n, a (4 * n) % 5 = 2 ∧ a (4 * n + 1) % 5 = 1 ∧ a (4 * n + 2) % 5 = 3 ∧ a (4 * n + 3) % 5 = 4 := by
        intro n
        induction n with 
        | zero => 
          exact ⟨rfl, rfl, rfl, rfl⟩
        | succ m ih => 
          obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
          have aux0 : a (4 * (m + 1)) % 5 = 2 := by
            have aux2 : a (4 * (m + 1)) = a (4 * m + 2 + 2) := by
                congr
            rw [aux2]
            unfold a
            rw [Nat.add_mod, ih2, ih3]
          have aux1 : a (4 * (m + 1) + 1) % 5 = 1 := by
            have aux2 : a (4 * (m + 1) + 1) = a (4 * m + 3 + 2) := by
              ring_nf
            rw [aux2]
            conv => 
              lhs
              unfold a 
            rw [Nat.add_mod, ih3, show 4 * m + 3 + 1 = 4 * (m + 1) by ring, aux0]
          have aux2 : a (4 * (m + 1) + 2) % 5 = 3 := by
            conv => 
              lhs 
              unfold a
            rw [Nat.add_mod, aux0, aux1]
          have aux3 : a (4 * (m + 1) + 3) % 5 = 4 := by
            conv =>
              lhs 
              unfold a
            rw [Nat.add_mod, aux1, aux2]
          exact ⟨aux0, aux1, aux2, aux3⟩
      obtain ⟨t, ht⟩ := hodd
      rw [ht]
      obtain eq1 := aux1 t
      have eq2 : (a (2 * (2 * t + 1) + 1)) = a (4 * t + 3) := by 
        ring_nf
      rw [eq2, peq5]
      omega
    -- the case p ≠ 5
    · 
      have pdvd : p ∣ fib k := by 
        norm_cast at hpk
        have pdvd_or : p ∣ 5 ∨ p ∣ fib k ^ 2 := by
          exact (Nat.Prime.dvd_mul hp).mp hpk
        obtain pdvd1 | pdvd2 := pdvd_or
        have prime5 : Nat.Prime 5 := by norm_num
        have peq5' : p = 5 := by 
          exact (Nat.prime_dvd_prime_iff_eq hp prime5).mp pdvd1
        by_contra _
        exact peq5 peq5'
        exact Nat.Prime.dvd_of_dvd_pow hp pdvd2
      by_cases hk0 : k = 0 
      -- the case k = 0
      · rw [hk0] at hpk' ⊢ 
        simp at hpk' ⊢
        unfold a at hpk' ⊢
        simp at hpk' ⊢
        norm_cast at hpk' ⊢
        rw [show 4 = 2 ^ 2 by norm_num] at hpk'
        exact Nat.Prime.dvd_of_dvd_pow hp hpk'
      · -- the case k ≥ 1 
        have kge1 : k ≥ 1 := by
          omega
        have aux1 : a (2 * k + 1) = a (2 * k - 1) + a (2 * k) := by 
          conv => 
            lhs
            rw [show 2 * k + 1 = 2 * k - 1 + 2 by omega]
            unfold a
            rw [show 2 * k - 1 + 1 = 2 * k by omega]
        rw [aux1]
        simp
        have aux2 : a (2 * k - 1) ≡ 1 [ZMOD p] := by 
          have eq1 : 2 * k - 1 = 2 * (k - 1) + 1 := by 
            omega
          rw [eq1, h5, show k - 1 + 1 = k by omega]
          have aux3 : (-1) ^ (k - 1) = 1 := by 
            have evenk : Even (k - 1) := by 
              refine Nat.Odd.sub_odd hodd ?_
              simp
            exact Even.neg_one_pow evenk
          rw [aux3]
          have aux4 : (a (k - 1) : ℤ) = a (k + 1) - a k := by 
            have eq_aux : a (k + 1) = a (k) + a (k - 1) := by 
              conv => 
                lhs
                rw [show k + 1 = k - 1 + 2 by omega]
                unfold a
              rw [show k - 1 + 1 = k by omega]
              ring
            rw [eq_aux]
            simp
          rw [aux4, h1 (k + 1) (by linarith), h1 k kge1]
          have aux5 : ((fib (k + 1 + 1) : ℤ) + fib (k + 1 - 1)) - ↑(fib (k + 1) + fib (k - 1)) = 2 * fib k - fib (k - 1) := by 
            have eq_aux : fib (k + 1 + 1) = fib (k) + fib (k + 1) := by
              rw [Nat.fib_add_two]
            rw [eq_aux, show k + 1 - 1 = k by omega]
            simp 
            ring_nf
          norm_num at aux5
          norm_num
          rw [aux5]
          obtain h2' := h2 k kge1 
          have aux6 : fib (k - 1) ^ 2 ≡ - 1 [ZMOD p] := by
            have eq_aux : ↑(fib (k - 1)) * ↑(fib (k + 1)) - ↑(fib k) ^ 2 ≡ (-1 : ℤ) ^ k [ZMOD p] := by 
              rw [h2']
            rw [aux] at eq_aux
            calc 
              _ ≡ fib (k - 1) * fib (k - 1) [ZMOD p] := by 
                congr
                ring
              _ ≡ fib (k - 1) * (fib (k + 1)) [ZMOD p] := by
                have eq_aux2 : fib (k - 1) ≡ fib (k + 1) [ZMOD p] := by 
                  rw [show k + 1 = k - 1+ 2 by omega, fib_add_two]
                  apply Int.modEq_of_dvd
                  simp
                  rw [show k - 1 + 1 = k by omega]
                  norm_cast
                exact Int.ModEq.mul_left (↑(fib (k - 1))) eq_aux2
              _ ≡ fib (k - 1) * (fib (k + 1)) - fib k ^ 2 [ZMOD p] := by 
                apply Int.modEq_of_dvd
                simp
                norm_cast
                refine Dvd.dvd.pow pdvd ?_
                linarith
              _ ≡ -1 [ZMOD p] := by
                exact eq_aux
          calc 
            _ ≡ - fib (k - 1) * fib (k + 1) - fib (k - 1) ^ 2 - 1 [ZMOD p] := by 
              apply Int.modEq_of_dvd
              simp
              ring_nf
              have dvd1 : (p : ℤ) ∣ -(↑(fib (k - 1)) * ↑(fib k) * 2) := by 
                obtain ⟨m, hm⟩ := pdvd
                use (- fib (k - 1) * 2 * m)
                rw [hm]
                ring_nf 
                simp
                norm_cast
                ring 
              have dvd2 : (p : ℤ) ∣ ↑(fib (1 + k)) * ↑(fib k) * 2 := by 
                obtain ⟨m, hm⟩ := pdvd
                use (fib (k + 1) * 2 * m)
                rw [hm]
                simp
                norm_cast
                ring_nf
              exact Int.dvd_sub dvd1 dvd2
            _ ≡ 1 [ZMOD p] := by 
              have eq_aux : -((fib (k - 1)) : ℤ) * ↑(fib (k + 1)) = 
                - (fib k) ^ 2 + 1 := by 
                rw [aux] at h2'
                linarith 
              rw [eq_aux]
              ring_nf
              calc 
                _ ≡ -↑(fib k) ^ 2 - (-1) [ZMOD p] := by 
                  exact Int.ModEq.sub_left (-↑(fib k) ^ 2) aux6
                _ ≡ 1 [ZMOD p] := by 
                  apply Int.modEq_of_dvd
                  ring_nf
                  norm_cast
                  refine Dvd.dvd.pow pdvd ?_
                  linarith
        obtain aux3 := Int.ModEq.dvd (Int.ModEq.symm aux2)
        have aux4 : ↑(a (2 * k - 1)) + ↑(a (2 * k)) + (1 : ℤ) = (↑(a (2 * k - 1)) - 1)
          + (a (2 * k) + 2) := by 
          ring
        rw [aux4]
        exact (Int.dvd_add_right aux3).mpr hpk'

