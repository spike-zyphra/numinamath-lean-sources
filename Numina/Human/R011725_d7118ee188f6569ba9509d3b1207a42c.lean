import Mathlib

/- Positive integers $m$ and $n$ satisfy $m n=5000$. If $m$ is not divisible by 10 and $n$ is not divisible by 10 , what is the value of $m+n$ ? -/
theorem number_theory_288078 (m n : ℕ)
  (hm : m > 0) (hn : n > 0) (hmn : m * n = 5000)
  (hdiv : ¬(10 ∣ m) ∧ ¬(10 ∣ n)) : m + n = 633 :=
by
  -- We note that $5000=5 \cdot 1000=5 \cdot 10^{3}=5 \cdot(2 \cdot 5)^{3}=5 \cdot 2^{3} \cdot 5^{3}=2^{3} 5^{4}$.
  have : 5000 = 2^3 * 5^4 := by rfl
  rw [this] at hmn
  rcases em (m = 2^3 ∨ n = 2^3) with(h|h)
  . -- Assume the value of $m$ or $n$ is $2^{3}$.
    -- Then both cases can be compute to the answer.
    rcases h with (h|h)
    . have : n = 5^4 := by
        rw [←h] at hmn
        exact Nat.eq_of_mul_eq_mul_left hm hmn
      subst h this
      simp
    . have : m = 5^4 := by
        rw [←h] at hmn
        rw [mul_comm] at hmn
        exact Nat.eq_of_mul_eq_mul_left hn hmn
      subst h this
      simp
  . -- Now we show that $m$ and $n$ can not have mixure prime factors of $2$ and $5$.
    -- which is trivial but very cumbersome.
    push_neg at h
    -- we first show that $m$ and $n$ are not pure powers of $2$ or $5$.
    rcases em (m = 5^4 ∨ n = 5^4) with (h1|h1)
    . rcases h1 with (h1|h1)
      . rw [h1, mul_comm] at hmn
        have : n = 2 ^ 3 := by
          apply Nat.eq_of_mul_eq_mul_right (m := 5^4)
          simp
          assumption
        subst h1 this
        simp
      . rw [h1] at hmn
        have : m = 2 ^ 3 := by
          apply Nat.eq_of_mul_eq_mul_right (m := 5^4)
          simp
          assumption
        subst h1 this
        simp
    .
      push_neg at h1
      exfalso
      let ⟨H, H'⟩ := hdiv
      have mchoice : ¬ 2 ∣ m ∨ ¬ 5 ∣ m := by
        rw [show 10 = 2*5 by simp] at H
        by_contra x
        push_neg at x
        let ⟨l,r⟩ := x
        apply H
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl l r
      exfalso
      -- $m \neq 1$.
      rcases em (m = 1) with (h3|h3)
      . rw [h3] at hmn
        simp at hmn
        rw [hmn] at hdiv
        tauto
      . let facls := [2,2,2,5,5,5,5]
        have faclsH : (2^3*5^4 : ℕ).primeFactorsList = facls := by
          simp [facls]
          have A : (2^3 : ℕ).primeFactorsList = [2,2,2] := by
            rw [show [2,2,2] = List.replicate 3 2 by simp]
            apply Nat.Prime.primeFactorsList_pow
            decide
          have B : (5^4 : ℕ).primeFactorsList = [5,5,5,5] := by
            rw [show [5,5,5,5] = List.replicate 4 5 by simp]
            apply Nat.Prime.primeFactorsList_pow
            decide
          have := Nat.perm_primeFactorsList_mul_of_coprime (a := 2^3) (b := 5^4) (by decide)
          rw [A,B] at this
          simp at this
          apply List.Perm.eq_of_sorted (le := Nat.le)
          . intros a b ha hb hab
            exact fun a_1 => Nat.le_antisymm hab a_1
          . have := Nat.primeFactorsList_sorted 5000
            simp [List.Sorted] at this
            assumption
          . simp
          . rw [ show [2,2,2,5,5,5,5] = [2,2,2] ++ [5,5,5,5] by simp
               , show 5000 = 2^3 * 5^4 by simp
               , ← A, ← B]
            apply Nat.perm_primeFactorsList_mul_of_coprime
            decide
        have msub : m.primeFactorsList.Sublist facls := by
          rw [←faclsH]
          apply Nat.primeFactorsList_sublist_of_dvd
          use n; linarith; decide
        have nsub : facls.Perm (m.primeFactorsList ++ n.primeFactorsList) := by
          rw [←faclsH, ←hmn]
          apply Nat.perm_primeFactorsList_mul
          linarith; linarith

        -- The two lemmas will be used very often.
        have mnpc2 : m.primeFactorsList.count 2 + n.primeFactorsList.count 2 = 3 := by
          rw [show 3 = facls.count 2 by decide]
          trans (m.primeFactorsList ++ n.primeFactorsList).count 2
          . exact Eq.symm (List.count_append 2 m.primeFactorsList n.primeFactorsList)
          . exact List.Perm.count_eq (id (List.Perm.symm nsub)) 2
        have mnpc5 : m.primeFactorsList.count 5 + n.primeFactorsList.count 5 = 4 := by
          rw [show 4 = facls.count 5 by decide]
          trans (m.primeFactorsList ++ n.primeFactorsList).count 5
          . exact Eq.symm (List.count_append 5 m.primeFactorsList n.primeFactorsList)
          . exact List.Perm.count_eq (id (List.Perm.symm nsub)) 5

        rcases mchoice with (h4|h4)
        . -- In this case, we use the `List.count` to process the prime factors.
          have nmemm2 : 2 ∉ m.primeFactorsList := by
            intro c
            apply h4
            exact Nat.dvd_of_mem_primeFactorsList c
          have memn2 : 2 ∈ n.primeFactors := by
            have mem2facls : 2 ∈ facls := by decide
            have : 2 ∈ m.primeFactorsList ++ n.primeFactorsList := (List.Perm.mem_iff nsub).mp mem2facls
            by_contra x
            apply List.not_mem_append
            exact nmemm2
            exact x
            simp
            simp at this
            assumption
          have nmemn5 : 5 ∉ n.primeFactorsList := by
            have : 2 ∣ n := Nat.dvd_of_mem_primeFactors memn2
            have : ¬ 5 ∣ n := by
              rw [show 10 = 2 * 5 by simp] at H'
              intro c
              apply H'
              exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl this c
            intro c
            apply this
            exact Nat.dvd_of_mem_primeFactorsList c
          have A : n.primeFactorsList.count 5 = 0 := List.count_eq_zero.mpr nmemn5
          rw [A] at mnpc5
          have B : m.primeFactorsList.count 2 = 0 := List.count_eq_zero.mpr ?_; swap; assumption
          rw [B] at mnpc2
          rw [show m.primeFactorsList.count 5 + 0 = m.primeFactorsList.count 5 by simp] at mnpc5
          rw [show 0 + n.primeFactorsList.count 2 = n.primeFactorsList.count 2 by simp] at mnpc2
          simp at A B
          have : ∀ x ∈ facls, x = 2 ∨ x = 5 := by decide
          have all2 : ∀ x ∈ n.primeFactorsList, x = 2 := by
            intro x h
            have H : x ∈ facls := by
              rw [←faclsH, ←hmn]
              simp
              simp at h
              constructor; tauto;
              constructor
              . have : x ∣ n := by tauto
                exact Dvd.dvd.mul_left this m
              . constructor; linarith; tauto
            rcases this x H with (h5|h5)
            . assumption
            . exfalso
              apply nmemn5
              rw [h5] at h
              exact h
          have : n.primeFactorsList.length = 3 := by
            have : List.count 2 n.primeFactorsList = List.count 2 (List.replicate n.primeFactorsList.length 2) := by
              rw [List.eq_replicate_of_mem all2]
              simp
            rw [←mnpc2, this, List.count_replicate_self]
          have : n.primeFactorsList = [2,2,2] := by
            rw [show [2,2,2] = List.replicate 3 2 by simp, List.eq_replicate_of_mem all2, this]
          apply h.2
          rw [←Nat.prod_primeFactorsList (n:=n), this]
          rfl
          linarith
        . -- This part is similar to the above.
          have nmemm5 : 5 ∉ m.primeFactorsList := by
            intro c
            apply h4
            exact Nat.dvd_of_mem_primeFactorsList c
          have memn5 : 5 ∈ n.primeFactors := by
            have mem5facls : 5 ∈ facls := by decide
            have : 5 ∈ m.primeFactorsList ++ n.primeFactorsList := (List.Perm.mem_iff nsub).mp mem5facls
            by_contra x
            apply List.not_mem_append
            exact nmemm5
            exact x
            simp
            simp at this
            assumption
          have nmemn5 : 2 ∉ n.primeFactorsList := by
            have : 5 ∣ n := Nat.dvd_of_mem_primeFactors memn5
            have : ¬ 2 ∣ n := by
              rw [show 10 = 2 * 5 by simp] at H'
              intro c
              apply H'
              exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl c this
            intro c
            apply this
            exact Nat.dvd_of_mem_primeFactorsList c
          have A : n.primeFactorsList.count 2 = 0 := List.count_eq_zero.mpr nmemn5
          rw [A] at mnpc2
          have B : m.primeFactorsList.count 5 = 0 := List.count_eq_zero.mpr ?_; swap; assumption
          rw [B] at mnpc5

          rw [show m.primeFactorsList.count 2 + 0 = m.primeFactorsList.count 2 by simp] at mnpc2
          rw [show 0 + n.primeFactorsList.count 5 = n.primeFactorsList.count 5 by simp] at mnpc5
          simp at A B
          have : ∀ x ∈ facls, x = 2 ∨ x = 5 := by decide
          have all5 : ∀ x ∈ n.primeFactorsList, x = 5 := by
            intro x h
            have H : x ∈ facls := by
              rw [←faclsH, ←hmn]
              simp
              simp at h
              constructor; tauto;
              constructor
              . have : x ∣ n := by tauto
                exact Dvd.dvd.mul_left this m
              . constructor; linarith; tauto
            rcases this x H with (h5|h5)
            . exfalso
              apply nmemn5
              rw [h5] at h
              exact h
            . assumption

          have : n.primeFactorsList.length = 4 := by
            have : List.count 5 n.primeFactorsList = List.count 5 (List.replicate n.primeFactorsList.length 5) := by
              rw [List.eq_replicate_of_mem all5]
              simp
            rw [←mnpc5, this, List.count_replicate_self]
          have : n.primeFactorsList = [5,5,5,5] := by
            rw [show [5,5,5,5] = List.replicate 4 5 by simp, List.eq_replicate_of_mem all5, this]
          apply h1.2
          rw [←Nat.prod_primeFactorsList (n:=n), this]
          rfl
          linarith
