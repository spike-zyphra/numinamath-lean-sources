import Mathlib

/- [ [Decimal numeral system ]

The sum of five numbers is 200. Prove that their product cannot end in 1999.

# -/
theorem number_theory_233273 (a b c d e : ℕ) (h₀ : a + b + c + d + e = 200) :
    ¬(∃ k, k = a * b * c * d * e ∧ k % 10000 = 1999) := by
        --We prove this by way of contradiction.
        by_contra h
        rcases h with ⟨k , hk⟩
        have hk₁ : k = a * b * c * d * e := by exact hk.1
        have hk₂ : k % 10000 = 1999 := by exact hk.2
        --Show it's not the case that Odd a ∧ Odd b ∧ Odd c ∧ Odd d ∧ Odd e by way of contradiction.
        have h₁ : ¬ (Odd a ∧ Odd b ∧ Odd c ∧ Odd d ∧ Odd e) := by
            by_contra h₁
            rcases h₁ with ⟨ha, hb, hc, hd, he⟩
            have ha1 : a % 2 = 1 := by exact Nat.odd_iff.mp ha
            have hb1 : b % 2 = 1 := by exact Nat.odd_iff.mp hb
            have hc1 : c % 2 = 1 := by exact Nat.odd_iff.mp hc
            have hd1 : d % 2 = 1 := by exact Nat.odd_iff.mp hd
            have he1 : e % 2 = 1 := by exact Nat.odd_iff.mp he
            --Simple modular arithmetic shows...
            have habcde1 : (a + b + c + d + e) % 2 = 1 := by omega
            rw [h₀] at habcde1
            contradiction

        -- Show ¬ Odd a ∨ ¬ Odd b ∨ ¬ Odd c ∨ ¬ Odd d ∨ ¬ Odd e
        have : ¬ Odd a ∨ ¬ Odd b ∨ ¬ Odd c ∨ ¬ Odd d ∨ ¬ Odd e := by tauto

        --Now we do a case analysis.
        
        by_cases
        h1' : ¬ Odd a
        have h1 : Even a := by exact Nat.not_odd_iff_even.mp h1'
        rcases h1 with ⟨ka , ha⟩
        rw [ha] at hk₁
        have h2 : k = 2 * (ka * b * c * d * e) := by linarith
        have h3 : k % 2 = 0 := by omega
        have h4 : k % 10000 ≠ 1999 := by omega
        contradiction

        have : ¬ Odd b ∨ ¬ Odd c ∨ ¬ Odd d ∨ ¬ Odd e := by tauto

        by_cases
        h1' : ¬ Odd b
        have h1 : Even b := by exact Nat.not_odd_iff_even.mp h1'
        rcases h1 with ⟨kb, hb⟩
        rw [hb] at hk₁
        have h2 : k = 2 * (a * kb * c * d * e) := by linarith
        have h3 : k % 2 = 0 := by omega
        have h4 : k % 10000 ≠ 1999 := by omega
        contradiction

        have : ¬ Odd c ∨ ¬ Odd d ∨ ¬ Odd e := by tauto

        by_cases
        h1' : ¬ Odd c
        have h1 : Even c := by exact Nat.not_odd_iff_even.mp h1'
        rcases h1 with ⟨kc, hc⟩
        rw [hc] at hk₁
        have h2 : k = 2 * (a * b * kc * d * e) := by linarith
        have h3 : k % 2 = 0 := by omega
        have h4 : k % 10000 ≠ 1999 := by omega
        contradiction

        have : ¬ Odd d ∨ ¬ Odd e := by tauto

        by_cases
        h1' : ¬ Odd d
        have h1 : Even d := by exact Nat.not_odd_iff_even.mp h1'
        rcases h1 with ⟨kd, hd⟩
        rw [hd] at hk₁
        have h2 : k = 2 * (a * b * c * kd * e) := by linarith
        have h3 : k % 2 = 0 := by omega
        have h4 : k % 10000 ≠ 1999 := by omega
        contradiction

        have : ¬ Odd e := by tauto

        by_cases
        h1' : ¬ Odd e
        have h1 : Even e := by exact Nat.not_odd_iff_even.mp h1'
        rcases h1 with ⟨ke, he⟩
        rw [he] at hk₁
        have h2 : k = 2 * (a * b * c * d * ke) := by linarith
        have h3 : k % 2 = 0 := by omega
        have h4 : k % 10000 ≠ 1999 := by omega
        contradiction

        --What we've proven contradicts h₁.
        contradiction