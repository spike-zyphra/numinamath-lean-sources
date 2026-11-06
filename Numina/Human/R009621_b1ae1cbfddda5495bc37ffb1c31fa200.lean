import Mathlib

/- Prove that for every polynomial $P(x)$ with real coefficients there exist a positive integer $m$ and polynomials $P_{1}(x), P_{2}(x), \ldots, P_{m}(x)$ with real coefficients such that

$$
P(x)=\left(P_{1}(x)\right)^{3}+\left(P_{2}(x)\right)^{3}+\cdots+\left(P_{m}(x)\right)^{3} .
$$ -/
theorem algebra_241700 {P : Polynomial ℝ} :
    ∃ m > 0, ∃ Q : ℕ → Polynomial ℝ,
      P = ∑ i ∈ Finset.range m, (Q i)^3 := by

  set k : ℕ := P.natDegree with hk
  -- set this proposition to induction
  suffices h : ∀P : Polynomial ℝ, P.natDegree ≤ k → ∃ m > 0, ∃ Q : ℕ → Polynomial ℝ,
      P = ∑ i ∈ Finset.range m, (Q i)^3 by
    apply h P
    rw [<-hk]

  -- set the proposition of cube root
  have cube_root (a : ℝ) : ∃b, b ^ 3 = a := by
    by_cases ha : 0 ≤ a
    -- when 0 ≤ a
    . use a^(1/(3 : ℝ))
      simp
      -- natCast
      suffices hb : (a ^ (3 : ℝ)⁻¹) ^ (3 : ℝ) = a by
        nth_rewrite 2 [<-hb]
        norm_cast
      rw [@Real.rpow_inv_rpow]
      tauto
      norm_num
    -- when a < 0
    . simp at ha
      use -(-a)^(1/(3 : ℝ))
      simp
      -- exactly extract -1 outside the parentheses
      have eq : (-(-a) ^ (3 : ℝ)⁻¹) ^ 3 = -((-a) ^ (3 : ℝ)⁻¹) ^ 3 := by
        calc
          (-(-a) ^ (3 : ℝ)⁻¹) ^ 3 = ((-1) * (-a) ^ (3 : ℝ)⁻¹) ^ 3 := by simp
          _ = (-1) ^ 3 * ((-a) ^ (3 : ℝ)⁻¹) ^ 3 := by rw [mul_pow]
          _ = -((-a) ^ (3 : ℝ)⁻¹) ^ 3 := by ring_nf
      rw [eq]
      -- natCast
      suffices hb : -((-a) ^ (3 : ℝ)⁻¹) ^ (3 : ℝ) = a by
        nth_rewrite 2 [<-hb]
        norm_cast
      rw [@Real.rpow_inv_rpow]
      ring_nf
      linarith only [ha]
      norm_num
  -- prove by induction
  induction k with
  | zero => -- when P.natDegree = 0
    intro P h
    rw [Nat.le_zero] at h
    rw [Polynomial.natDegree_eq_zero] at h
    obtain ⟨a, haP⟩ := h
    -- base case
    use 1, Nat.zero_lt_one
    -- have that b ^ 3 = a
    obtain ⟨b, hb⟩ := cube_root a
    -- back to prove P = b ^ 3
    use fun _ => Polynomial.C b
    simp
    rw [<-Polynomial.C_pow, hb, haP]
  -- induction step
  | succ d hd =>
    intro P hP
    -- divide cases by P.natDegree ≤ d
    rw [Nat.le_succ_iff_eq_or_le] at hP
    cases hP with
    -- when P.natDegree ≤ d, easily
    | inr hP => apply hd P hP
    | inl hP => -- when P.natDegree > d, i.e P.natDegree = d + 1
      simp at hP
      -- divide into three cases
      obtain ⟨k, hdk⟩ : ∃k, d + 1 = 3 * k ∨ d + 1 = 3 * k + 1 ∨ d + 1= 3 * k + 2 := by
        -- prove by induction
        clear hd hP
        induction d with
        | zero => use 0; simp
        | succ d hd => -- show that d + 1 satisfied
          obtain ⟨k, hk | hk | hk⟩ := hd
          . -- when d = 3 * k
            use k
            right; left
            rw [hk]
          . -- when d = 3 * k + 1
            use k
            right; right
            rw [hk]
          . -- when d = 3 * k + 2
            use k + 1
            left
            rw [hk]; ring_nf

      -- rewrite the conclusion
      suffices h : ∃m > 0, ∃Q : ℕ → Polynomial ℝ, (Polynomial.monomial P.natDegree) P.leadingCoeff =
          ∑ i ∈ Finset.range m, (Q i)^3 by
        obtain ⟨m1, hm1, Q1, hQ1⟩ := h
        -- show the natdegree of P.eraseLead
        have herase : P.eraseLead.natDegree ≤ d := by
          rw [show d = P.natDegree - 1 by rw [hP]; norm_num]
          apply Polynomial.eraseLead_natDegree_le
        apply hd at herase -- so that we can use the induction hypothesis
        obtain ⟨m2, hm2, Q2, hQ2⟩ := herase

        -- so we can construct the final polynomial list
        use (m1 + m2)
        refine ⟨?_, ?_⟩
        . positivity -- m1 + m2 > 0
        -- construct the polynomial list
        . let Q : ℕ → Polynomial ℝ := fun i => if i < m1 then Q1 i else Q2 (i - m1)
          use Q
          -- show the polynomial list is correct
          have hQ : ∑ i ∈ Finset.range (m1 + m2), (Q i)^3 = ∑ i ∈ Finset.range m1, (Q1 i)^3 + ∑ i ∈ Finset.range m2, (Q2 i)^3 := by
            rw [Finset.sum_range_add]
            simp [Q]
            rw [Finset.sum_congr]
            rfl
            intro x hx
            simp at hx
            simp [hx]
          rw [<-hQ1, <-hQ2, <-Polynomial.self_sub_monomial_natDegree_leadingCoeff] at hQ
          ring_nf at hQ
          exact hQ.symm

      -- divide cases by d
      rcases hdk with hk | hk | hk
      . -- when d + 1 = 3 * k
        obtain ⟨c, hc⟩ := cube_root (P.leadingCoeff)
        set Q1 : Polynomial ℝ := Polynomial.C c * Polynomial.X ^ k with hQ1
        -- calculate the cube sum of Q1, Q2, Q3
        have hcube_sum : Q1 ^ 3 = (Polynomial.monomial P.natDegree) P.leadingCoeff := by
          rw [hQ1]
          calc
            Q1 ^ 3 = (Polynomial.C c^3) * ((Polynomial.X ^ k) ^ 3) := by
              ring_nf
            _ = Polynomial.C (P.leadingCoeff) * Polynomial.X ^ (3 * k) := by
              rw [<-Polynomial.C_pow, hc]
              ring_nf
            -- finally we calculate from the reverse
            _ = Polynomial.monomial P.natDegree P.leadingCoeff := by
              rw [<-hk, <-hP]
              symm
              calc
                (Polynomial.monomial P.natDegree) P.leadingCoeff = (Polynomial.monomial P.natDegree) (1 * P.leadingCoeff) := by ring_nf
                _ = (Polynomial.monomial P.natDegree) 1 * Polynomial.C P.leadingCoeff := by
                  rw [Polynomial.monomial_mul_C]
                _ = Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree := by
                  rw [Polynomial.monomial_one_right_eq_X_pow]
                  ring_nf
        -- finally get the conclusion
        use 1
        norm_num
        let Q : ℕ → Polynomial ℝ := fun _ => Q1
        use Q
        simp [Finset.sum, Q]
        rw [<-hcube_sum]
      . -- when d + 1 = 3 * k + 1
        -- set some basic value
        obtain ⟨c1, hc1⟩ := cube_root (P.leadingCoeff / 3)
        obtain ⟨c2, hc2⟩ := cube_root (P.leadingCoeff / 6)
        set Q1 : Polynomial ℝ := Polynomial.C c2 * Polynomial.X ^ k * (Polynomial.X + Polynomial.C 1)
        set Q2 : Polynomial ℝ := Polynomial.C c2 * Polynomial.X ^ k * (Polynomial.X - Polynomial.C 1)
        set Q3 : Polynomial ℝ := -Polynomial.C c1 * Polynomial.X ^ (k + 1)
        -- calculate the cube sum of Q1, Q2, Q3
        have hcube_sum : Q1 ^ 3 + Q2 ^ 3 + Q3 ^ 3 = (Polynomial.monomial P.natDegree) P.leadingCoeff := by
          calc
            Q1 ^ 3 + Q2 ^ 3 + Q3 ^ 3 = (Polynomial.C c2^3) * ((Polynomial.X ^ k) ^ 3) * ((Polynomial.X + Polynomial.C 1) ^ 3) +
                (-Polynomial.C c1^3) * ((Polynomial.X ^ (k + 1)) ^ 3) +
                (Polynomial.C c2^3) * ((Polynomial.X ^ k) ^ 3) * ((Polynomial.X - Polynomial.C 1) ^ 3) := by
              ring_nf
            _ = (Polynomial.C (c2^3)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X + Polynomial.C 1) ^ 3) +
                (-Polynomial.C (c1^3)) * (Polynomial.X ^ (3 * k)) * (Polynomial.X ^ 3) +
                (Polynomial.C (c2^3)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X - Polynomial.C 1) ^ 3) := by
              repeat rw [Polynomial.C_pow]
              ring_nf
            -- substitute the coefficients
            _ = (Polynomial.C (P.leadingCoeff / 6)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X + Polynomial.C 1) ^ 3) +
                (-Polynomial.C (P.leadingCoeff / 3)) * (Polynomial.X ^ (3 * k)) * (Polynomial.X ^ 3) +
                (Polynomial.C (P.leadingCoeff / 6)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X - Polynomial.C 1) ^ 3) := by
              rw [hc1, hc2]
            -- extract the common factor
            _ = (Polynomial.C (P.leadingCoeff / 6)) * (Polynomial.X ^ (3 * k)) *
                ((Polynomial.X + Polynomial.C 1) ^ 3 + (Polynomial.X - Polynomial.C 1) ^ 3 - Polynomial.C 2 * Polynomial.X ^ 3) := by
              rw [show Polynomial.C (P.leadingCoeff / 3) = Polynomial.C 2 * Polynomial.C (P.leadingCoeff / 6) by rw [<-Polynomial.C_mul]; ring_nf]
              ring_nf
            -- simplify the polynomial
            _ = Polynomial.C (P.leadingCoeff * (1 / 6)) * Polynomial.X * Polynomial.X ^ (k * 3) * Polynomial.C 1 ^ 2 * 6 := by
              rw [show Polynomial.C 2 = (2 : Polynomial ℝ) by norm_cast]
              ring_nf
            _ = (Polynomial.C (P.leadingCoeff / 6) * Polynomial.C 6) * Polynomial.X ^ (3 * k + 1) := by
              rw [show (6 : Polynomial ℝ) = Polynomial.C 6 by norm_cast]
              rw [show Polynomial.C 1 = (1 : Polynomial ℝ) by norm_cast]
              ring_nf
            _ = Polynomial.C (P.leadingCoeff) * Polynomial.X ^ (3 * k + 1) := by
              rw [<-Polynomial.C_mul]
              ring_nf
            -- finally we calculate from the reverse
            _ = Polynomial.monomial P.natDegree P.leadingCoeff := by
              rw [<-hk, <-hP]
              symm
              calc
                (Polynomial.monomial P.natDegree) P.leadingCoeff = (Polynomial.monomial P.natDegree) (1 * P.leadingCoeff) := by ring_nf
                _ = (Polynomial.monomial P.natDegree) 1 * Polynomial.C P.leadingCoeff := by
                  rw [Polynomial.monomial_mul_C]
                _ = Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree := by
                  rw [Polynomial.monomial_one_right_eq_X_pow]
                  ring_nf

        -- finally get the conclusion
        use 3
        norm_num
        let Q : ℕ → Polynomial ℝ := fun i => if i = 0 then Q1 else if i = 1 then Q2 else Q3
        use Q
        simp [Finset.sum, Q]
        rw [<-hcube_sum]
        ring_nf

      . -- when d + 1 = 3 * k + 2
        -- set some basic value
        obtain ⟨c1, hc1⟩ := cube_root (P.leadingCoeff / 3)
        obtain ⟨c2, hc2⟩ := cube_root (P.leadingCoeff / 6)
        set Q1 : Polynomial ℝ := Polynomial.C c2 * Polynomial.X ^ k * (Polynomial.X + Polynomial.C 1)
        set Q2 : Polynomial ℝ := -Polynomial.C c2 * Polynomial.X ^ k * (Polynomial.X - Polynomial.C 1)
        set Q3 : Polynomial ℝ := -Polynomial.C c1 * Polynomial.X ^ k
        -- calculate the cube sum of Q1, Q2, Q3
        have hcube_sum : Q1 ^ 3 + Q2 ^ 3 + Q3 ^ 3 = (Polynomial.monomial P.natDegree) P.leadingCoeff := by
          calc
            Q1 ^ 3 + Q2 ^ 3 + Q3 ^ 3 = (Polynomial.C c2^3) * ((Polynomial.X ^ k) ^ 3) * ((Polynomial.X + Polynomial.C 1) ^ 3) +
                (-Polynomial.C c1^3) * ((Polynomial.X ^ k) ^ 3) +
                (-Polynomial.C c2^3) * ((Polynomial.X ^ k) ^ 3) * ((Polynomial.X - Polynomial.C 1) ^ 3) := by
              ring_nf
            _ = (Polynomial.C (c2^3)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X + Polynomial.C 1) ^ 3) +
                (-Polynomial.C (c1^3)) * (Polynomial.X ^ (3 * k)) +
                (-Polynomial.C (c2^3)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X - Polynomial.C 1) ^ 3) := by
              repeat rw [Polynomial.C_pow]
              ring_nf
            -- substitute the coefficients
            _ = (Polynomial.C (P.leadingCoeff / 6)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X + Polynomial.C 1) ^ 3) +
                (-Polynomial.C (P.leadingCoeff / 3)) * (Polynomial.X ^ (3 * k)) +
                (-Polynomial.C (P.leadingCoeff / 6)) * (Polynomial.X ^ (3 * k)) * ((Polynomial.X - Polynomial.C 1) ^ 3) := by
              rw [hc1, hc2]
            -- extract the common factor
            _ = (Polynomial.C (P.leadingCoeff / 6)) * (Polynomial.X ^ (3 * k)) *
                ((Polynomial.X + Polynomial.C 1) ^ 3 - (Polynomial.X - Polynomial.C 1) ^ 3 - Polynomial.C 2) := by
              rw [show Polynomial.C (P.leadingCoeff / 3) = Polynomial.C 2 * Polynomial.C (P.leadingCoeff / 6) by rw [<-Polynomial.C_mul]; ring_nf]
              ring_nf
            -- simplify the polynomial
            _ = Polynomial.C (P.leadingCoeff * (1 / 6)) * Polynomial.X ^ 2 * Polynomial.X ^ (k * 3) * Polynomial.C 1 * 6 := by
              rw [show Polynomial.C 2 = (2 : Polynomial ℝ) by norm_cast]
              rw [show Polynomial.C 1 = (1 : Polynomial ℝ) by norm_cast]
              ring_nf
            _ = (Polynomial.C (P.leadingCoeff / 6) * Polynomial.C 6) * Polynomial.X ^ (3 * k + 2) := by
              rw [show (6 : Polynomial ℝ) = Polynomial.C 6 by norm_cast]
              rw [show Polynomial.C 1 = (1 : Polynomial ℝ) by norm_cast]
              ring_nf
            _ = Polynomial.C (P.leadingCoeff) * Polynomial.X ^ (3 * k + 2) := by
              rw [<-Polynomial.C_mul]
              ring_nf
            -- finally we calculate from the reverse
            _ = Polynomial.monomial P.natDegree P.leadingCoeff := by
              rw [<-hk, <-hP]
              symm
              calc
                (Polynomial.monomial P.natDegree) P.leadingCoeff = (Polynomial.monomial P.natDegree) (1 * P.leadingCoeff) := by ring_nf
                _ = (Polynomial.monomial P.natDegree) 1 * Polynomial.C P.leadingCoeff := by
                  rw [Polynomial.monomial_mul_C]
                _ = Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree := by
                  rw [Polynomial.monomial_one_right_eq_X_pow]
                  ring_nf

        -- finally get the conclusion
        use 3
        norm_num
        let Q : ℕ → Polynomial ℝ := fun i => if i = 0 then Q1 else if i = 1 then Q2 else Q3
        use Q
        simp [Finset.sum, Q]
        rw [<-hcube_sum]
        ring_nf
