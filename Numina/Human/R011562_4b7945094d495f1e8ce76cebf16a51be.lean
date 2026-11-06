import Mathlib

/- 301. Show that the sum of the squares of ten consecutive numbers cannot be a perfect square. -/
theorem number_theory_258338 (n : ℤ) :
    ¬ ∃ m, m^2 = n^2 + (n+1)^2 + (n+2)^2 + (n+3)^2 + (n+4)^2 +
      (n+5)^2 + (n+6)^2 + (n+7)^2 + (n+8)^2 + (n+9)^2 := by
        --We prove this by way of contradiction.
        by_contra h
        obtain ⟨m,hm⟩ := h
        --We simplify the sum and obtain the following.
        have h1 : n^2 + (n+1)^2 + (n+2)^2 + (n+3)^2 + (n+4)^2 + (n+5)^2 + (n+6)^2 + (n+7)^2 + (n+8)^2 + (n+9)^2 = 10 * n^2 + 90 * n + 285 := by
          ring
        --Factoring out a five from 10 * n^2 + 90 * n + 285 yields the following.
        have h2 : 10 * n^2 + 90 * n + 285 = 5 * (2 * n^2+ 18 * n + 57) := by ring
        --Substituting h2 to hm gives the following.
        rw [h1] at hm
        rw [h2] at hm
        --We claim that five must divide 2 * n^2+ 18 * n + 57.
        --This is so owing to the facts that 5 is a prime number and 5 * (2 * n^2+ 18 * n + 57) is a perfect square.
        have h3 : (2 * n^2+ 18 * n + 57) % 5 = 0 := by
          --Clearly 5 divides m^2
          have h31 : 5 ∣ m^2 := by omega
          --Since 5 is prime 5 divides m.
          have h32 : Prime 5 := by
            refine Nat.prime_iff.mp ?_
            decide
          have h33' : 5 ∣ m ∨ 5 ∣ m := by
            rw [pow_two] at hm
            --Prime.dvd_mul
            refine (Prime.dvd_mul ?_).mp ?_
            norm_num
            omega
          have h33 : 5 ∣ m := by tauto

          --Obtain k₁ and k₂.
          obtain ⟨k₁,hm₁⟩ := h31
          obtain ⟨k₂,hm₂⟩ := h33
          --Show k₁ = 5 * k₂^2.
          have h34 : k₁ = 5 * k₂^2 := by
            rw [pow_two] at hm₁
            rw [hm₂] at hm₁
            ring_nf at hm₁
            omega
          --Then we obtain 2 * n^2+ 18 * n + 57 = 5 * k₂^2
          have h35 : 2 * n^2+ 18 * n + 57 = 5 * k₂^2 := by
            rw [pow_two] at hm
            rw [hm₂] at hm
            have h351 : 5 * k₂ * (5 * k₂) = 25 * k₂^2 := by ring
            rw [h351] at hm
            omega
          --Hence 5 divides 2 * n^2+ 18 * n + 57 as claimed.

          rw [h35]
          exact Int.mul_emod_right 5 (k₂ ^ 2)



        --Now we notice the following.

        have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
        rcases h4 with (h₀|h₁|h₂|h₃|h₄)

        --Case : n % 5 = 0.
        have h5 : (2 * n ^ 2 + 18 * n + 57) % 5 = 57 := by
          --rw [Nat.add_mod, Nat.pow_mod]
          have h51 : (2 * n ^ 2 + 18 * n) % 5 = 0 := by
            refine Int.emod_eq_zero_of_dvd ?_
            have : 5 ∣ n := by omega
            refine (Int.dvd_add_right ?_).mpr ?_
            obtain ⟨k, hk⟩ := this
            rw [hk]
            have : 2 * (5 * k) ^ 2 = 5 * (10 * k^2) := by ring
            rw [this]
            use (10 * k^2)
            obtain ⟨k, hk⟩ := this
            rw [hk]
            have : 18 * (5 * k) = 5 * (18 * k) := by ring
            rw [this]
            use 18 * k
          omega
        --Thus we have a contradiction.
        have : 0 = 57 := by omega
        contradiction

        --Case n % 5 = 1
        have h6 : (2 * n ^ 2 + 18 * n + 57) % 5 = 2 := by
          have h61 : 2 * n ^ 2 + 18 * n + 57 = (n - 1) * (2 * n + 20) + 77 := by ring
          have h62 : (n - 1) % 5 = 0 := by omega
          simp_all only [EuclideanDomain.mod_eq_zero]
          obtain ⟨k, hk⟩ :=  h62
          rw [hk]
          ring_nf
          omega
        have : 0 = 2 := by omega
        contradiction

        --Case n % 5 = 2
        have h7 : (2 * n ^ 2 + 18 * n + 57) % 5 = 1 := by
          have h71 : 2 * n ^ 2 + 18 * n + 57 = (n - 2) * (2 * n + 22) + 101 := by ring
          have h72 : (n - 2) % 5 = 0 := by omega
          simp_all only [EuclideanDomain.mod_eq_zero]
          obtain ⟨k, hk⟩ :=  h72
          rw [hk]
          ring_nf
          omega
        have : 0 = 1 := by omega
        contradiction

        --Case n % 5 = 3
        have h8 : (2 * n ^ 2 + 18 * n + 57) % 5 = 4 := by
          have h81 : 2 * n ^ 2 + 18 * n + 57 = (n - 3) * (2 * n + 24) + 129 := by ring
          have h82 : (n - 3) % 5 = 0 := by omega
          simp_all only [EuclideanDomain.mod_eq_zero]
          obtain ⟨k, hk⟩ :=  h82
          rw [hk]
          ring_nf
          omega
        have : 0 = 4 := by omega
        contradiction

        --Case n % 5 = 4
        have h9 : (2 * n ^ 2 + 18 * n + 57) % 5 = 1 := by
          have h91 : 2 * n ^ 2 + 18 * n + 57 = (n - 4) * (2 * n + 26) + 161 := by ring
          have h92 : (n - 4) % 5 = 0 := by omega
          simp_all only [EuclideanDomain.mod_eq_zero]
          obtain ⟨k, hk⟩ :=  h92
          rw [hk]
          ring_nf
          omega
        have : 0 = 1 := by omega
        contradiction

        --Done.