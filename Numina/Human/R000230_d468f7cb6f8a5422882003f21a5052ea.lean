import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all primes  $p$  and  $q$  such that  $p$  divides  $q^2-4$  and
  $q$  divides  $p^2-1$ .-/
theorem number_theory_8637 :
  {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ p ∣ q^2 - 4 ∧ q ∣ p^2 - 1} =
  {(5, 3)} ∪ {(p, q) : ℕ × ℕ| p.Prime ∧ Odd p ∧ q = 2}:= by
    ext x; simp; constructor
    · intro ⟨hp, hq, pdvd, qdvd⟩
      -- Here `x.1` is $p$ and `x.2` is $q$.
      by_cases qeven : Even x.2
      · -- If  $q$  is even then  $q=2$  so   $(p,q)=(p,2)$  ,  $p\neq2$ .
        have : x.2 = 2 := (Prime.even_iff hq).mp qeven
        simp [this] at qdvd
        -- If  $p$  even then  $p=2$  so no solutions. So $p$ is odd.
        have podd : Odd x.1 := by
          have c1 : Even (x.1^2 - 1) := (even_iff_exists_two_nsmul (x.1 ^ 2 - 1)).mpr qdvd
          obtain ⟨k, hk⟩ := c1
          have : Odd (x.1^2) := ⟨k, by
            simp [←two_mul] at hk
            rw [←hk, Nat.sub_add_cancel ]
            refine one_le_pow 2 x.1 ?h
            exact Prime.pos hp⟩
          exact Odd.of_mul_right this
        right
        exact ⟨hp, podd, this⟩
      · -- If now  $p$  odd (and  $q$  odd ) then  $p|q-2$  or $p|q+2$ so $\boxed{p\leq{q+2}}$    (1)
        have c1 : x.1 ≤ x.2 + 2 := by
          rw [show 4 = 2^2 by decide, sq_sub_sq] at pdvd
          rw [Nat.Prime.dvd_mul hp] at pdvd
          rcases pdvd with hl | hr
          · exact le_of_dvd (by omega) hl
          · have : 2 < x.2 := by
              have : 2 ≤ x.2 := by exact Prime.two_le hq
              refine Nat.lt_of_le_of_ne this ?h₂
              intro h
              simp [←h] at qeven
            exact (le_of_dvd (by omega) hr).trans (by omega)
        have podd : Odd x.1 := by
          simp at qeven
          have : Odd (x.2^2 - 4) := by
            have : Odd (x.2^2) := Odd.pow qeven
            refine Nat.Odd.sub_even ?_ this ?hn
            rw [show 4 = 2^2 by omega]
            refine Nat.pow_le_pow_of_le_left (Prime.two_le hq) 2
            decide
          exact Odd.of_dvd_nat this pdvd
        obtain ⟨k, hk⟩ := podd
        -- Also  $q|p-1$  or  $q|p+1$  but  $p$  odd so  $q|\dfrac{p-1}{2}$  or
        -- $q|\dfrac{p+1}{2}$  so  $\boxed{q\leq{\dfrac{p+1}{2}}}$   (2)
        have c2 : x.2 ≤ k + 1 := by
          have : x.2 ∣ (x.1 + 1) ∨ x.2 ∣ (x.1 - 1) := by
            rw [show x.1^2 - 1 = (x.1 + 1) * (x.1 - 1) by exact (Nat.sq_sub_sq x.1 1)] at qdvd
            exact (Nat.Prime.dvd_mul hq).mp qdvd
          have : x.2 ∣ k + 1 ∨ x.2 ∣ k := by
            simp [hk] at this
            rw [ show 2 * k + 1 + 1 = 2 * (k + 1) by linarith] at this
            rcases this with hl | hr
            · exact Or.inl <| (Nat.Coprime.dvd_mul_left
                (Odd.coprime_two_right (not_even_iff_odd.mp qeven))).1 hl
            · exact Or.inr <| (Nat.Coprime.dvd_mul_left
                (Odd.coprime_two_right (not_even_iff_odd.mp qeven))).1 hr
          rcases this with hl |hr
          · exact le_of_dvd (by simp) hl
          · have : 0 < k := by
              by_contra tmp
              have tmp : k = 0 := by omega
              simp [tmp] at hk
              exact Nat.not_prime_one (hk ▸ hp)
            exact (le_of_dvd this hr).trans (by omega)
        have  : k ≤ 2 := by linarith
        -- From  $(1),(2)$ $p\leq5$, $q\leq3$ so finally $(p,q)=(p,2)$ with $p\neq3$ and $(5,3)$
        have ple5 : x.1 ≤ 5 := by linarith
        have qle3 : x.2 ≤ 3 := by linarith
        simp [ Prod.eq_iff_fst_eq_snd_eq]
        interval_cases x.1 <;> (interval_cases x.2 <;> tauto)
    · intro h
      rcases h with hl | hr
      · simp [hl]
        exact ⟨Nat.prime_five, Nat.prime_three, by decide⟩
      · simp [hr]
        exact ⟨Nat.prime_two, by
          obtain ⟨k, hk⟩ := Odd.pow hr.2.1 (n := 2)
          simp [hk]⟩
