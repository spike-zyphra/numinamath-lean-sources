import Mathlib


open Nat


lemma lemma_1 (p k : ℕ) (hp : Nat.Prime p) (hk : 0 < k) (hdiv : ¬p ∣ k) :
    ¬∃ x y : ℕ, 0 < x ∧ 0 < y ∧ p * x * y = k := by
  rintro ⟨x, y, hx, hy, h_eq⟩
  have h1 : p ∣ k := by
    use (x * y)
    all_goals
      nlinarith
  exfalso
  exact hdiv h1


theorem number_theory_97969 :
    {(a, b, c, d, e, f, g) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
    a * b * c = 70 ∧
    c * d * e = 71 ∧
    e * f * g = 72}.ncard = 96 := by 
  have h1 : {(a, b, c, d, e, f, g) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ |
      a * b * c = 70 ∧
      c * d * e = 71 ∧
      e * f * g = 72} = Finset.filter (fun s : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      s.1 * s.2.1 * s.2.2.1 = 70 ∧
      s.2.2.1 * s.2.2.2.1 * s.2.2.2.2.1 = 71 ∧
      s.2.2.2.2.1 * s.2.2.2.2.2.1 * s.2.2.2.2.2.2 = 72) (Finset.Icc (0 : ℕ) 70 ×ˢ Finset.Icc (0 : ℕ) 70 ×ˢ (Finset.filter (fun x : ℕ => x = 1) (Finset.Icc (0 : ℕ) 1)) ×ˢ (Finset.filter (fun x : ℕ => x = 71) (Finset.Icc (0 : ℕ) 71)) ×ˢ (Finset.filter (fun x : ℕ => x = 1) (Finset.Icc (0 : ℕ) 1)) ×ˢ (Finset.filter (fun x : ℕ => x ≥ 1 ∧ x ≤ 72) (Finset.Icc (0 : ℕ) 72)) ×ˢ (Finset.filter (fun x : ℕ => x ≥ 1 ∧ x ≤ 72) (Finset.Icc (0 : ℕ) 72)
  )) := by 
    ext ⟨a, b, c, d, e, f, g⟩
    simp
    intro h1 h2 h3
    have ha1 : a > 0 := by
      by_contra h
      have : a = 0 := by omega
      rw [this] at h1
      nlinarith
    have hb1 : b > 0 := by
      by_contra h
      have : b = 0 := by omega
      rw [this] at h1
      nlinarith
    have hc1 : c > 0 := by
      by_contra h
      have : c = 0 := by omega
      rw [this] at h1
      nlinarith
    have hd1 : d > 0 := by
      by_contra h
      have : d = 0 := by omega
      rw [this] at h2
      nlinarith
    have he1 : e > 0 := by
      by_contra h
      have : e = 0 := by omega
      rw [this] at h2
      nlinarith
    have hf1 : f > 0 := by
      by_contra h
      have : f = 0 := by omega
      rw [this] at h3
      nlinarith
    have hg1 : g > 0 := by
      by_contra h
      have : g = 0 := by omega
      rw [this] at h3
      nlinarith
    have ha2 : a ≤ 70 := by
      have : a ∣ 70 := by
        use b * c
        all_goals
          nlinarith
      have h1 : a ≤ 70 := by
        exact Nat.le_of_dvd (by norm_num) this
      omega
    have hb2 : b ≤ 70 := by
      have : b ∣ 70 := by
        use a * c
        all_goals
          nlinarith
      have h1 : b ≤ 70 := by
        exact Nat.le_of_dvd (by norm_num) this
      omega
    have hc2 : c = 1 := by
      have hc5557 : c = 1 ∨ c = 71 := by
        have hc5555 : c ∣ 71 := by
          use (d * e)
          all_goals
            nlinarith
        have hc8855 : c ≤ 71 := by
          exact Nat.le_of_dvd (by norm_num) hc5555
        have hc8859 : c > 0 := by
          omega
        have hc88557 : c = 1 ∨ c = 71 := by
          interval_cases c <;> norm_num at hc5555 ⊢ 
          <;> try { tauto }
          <;> tauto
        tauto
      cases hc5557 with
      | inl hc757 =>
        omega -- e = 1
      | inr hc757 =>
        -- So c=71, plug into first equation:
        -- This gives a * b * 71 = 70, which is clearly false.
        have hc8445 : c = 71 := by omega
        rw [hc8445] at h1
        omega
    have hd22 : d = 71 := by
      -- From second equation c * d * e = 71, and setting c=1, e=1
      have hc6 : c = 1 := hc2
      have he4 : e = 1 := by
        have h14 : e ∣ 71 := by
          use (c * d)
          all_goals
            nlinarith
        have h15 : e ∣ 72 := by
          use (f * g)
          all_goals
            nlinarith
        -- Therefore e = 1
        have h4 : e = 1 := by
          have h35 : e ∣ 71 := h14
          have h42 : e ∣ 72 := h15
          have h53 : e ∣ Nat.gcd 71 72 := Nat.dvd_gcd h14 h15
          have h54 : Nat.gcd 71 72 = 1 := by
            norm_num [Nat.gcd]
          rw [h54] at h53
          have h68 : e = 1 := by
            have h66 : e ∣ 1 := h53
            have h65 : e = 1 := by 
              exact Nat.eq_one_of_dvd_one h66
            omega
          tauto
        omega
      -- Now c=1 and e=1, from second equation: 1 * d * 1 = 71 => d=71
      have hc66 : c = 1 := hc2
      have hc77 : e = 1 := he4
      have hc777 : c * d * e = 71 := by nlinarith [h2]
      rw [hc66, hc77] at hc777
      omega
    have he4 : e = 1 := by
      have h14 : e ∣ 71 := by
        use (c * d)
        all_goals
          nlinarith
      have h15 : e ∣ 72 := by
        use (f * g)
        all_goals
          nlinarith
      -- Therefore e = 1
      have h4 : e = 1 := by
        have h35 : e ∣ 71 := h14
        have h42 : e ∣ 72 := h15
        have h53 : e ∣ Nat.gcd 71 72 := Nat.dvd_gcd h14 h15
        have h54 : Nat.gcd 71 72 = 1 := by
          norm_num [Nat.gcd]
        rw [h54] at h53
        have h68 : e = 1 := by
          have h66 : e ∣ 1 := h53
          have h65 : e = 1 := by 
            exact Nat.eq_one_of_dvd_one h66
          omega
        tauto
      omega
    have hf2 : f ≤ 72 := by
      have h11 : f ∣ 72 := by
        use (e * g)
        all_goals
          nlinarith
      have h21 : f ≤ 72 := by
        exact Nat.le_of_dvd (by norm_num) h11
      omega
    have hg2 : g ≤ 72 := by
      have h11 : g ∣ 72 := by
        use (e * f)
        all_goals
          nlinarith
      have h21 : g ≤ 72 := by
        exact Nat.le_of_dvd (by norm_num) h11
      omega
    simp [hc2, hd22, he4]
    <;> norm_num 
    <;> omega
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide