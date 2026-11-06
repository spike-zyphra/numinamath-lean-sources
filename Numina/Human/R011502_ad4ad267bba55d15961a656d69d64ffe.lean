import Mathlib

/- ## Task 22/81

We are looking for all natural numbers $n$ that satisfy the equation $p_{2}^{3}-2=p_{1} \cdot n$; here, $p_{1} ; p_{2}$ is a prime twin pair. -/
theorem number_theory_159209 (n : ℕ) :
    (∃ p1 p2, Nat.Prime p1 ∧ Nat.Prime p2 ∧ p2^3 - 2 = p1 * n ∧ p2 = p1 + 2) ↔ n = 41 := by
      constructor <;> intro H
      obtain ⟨p₁, p₂, hp₁, hp₂, hp, htwin⟩ := H
      --Consider the following chain of  identities.
      have H1 : p₂^3 - 2 = (p₁ + 2)^3 - 2 := by
        exact congrFun (congrArg HSub.hSub (congrFun (congrArg HPow.hPow htwin) 3)) 2
      have H2 : (p₁ + 2)^3 - 2 = p₁^3 + 6 * p₁^2 + 12 * p₁ + 8 - 2 := by
        ring_nf
      have H3 : p₁^3 + 6 * p₁^2 + 12 * p₁ + 8 - 2 = p₁^3 + 6 * p₁^2 + 12 * p₁ + 6 := by
        exact rfl
      have H4 : p₁^3 + 6 * p₁^2 + 12 * p₁ + 6 = n * p₁ := by linarith
      --This means p₁ divides p₁^3 + 6 * p₁^2 + 12 * p₁ + 6.
      have H5 : p₁ ∣ p₁^3 + 6 * p₁^2 + 12 * p₁ + 6 := by
        rw [H4]
        use n
        ring
      --Obviously p₁ ∣  p₁^3 + 6 * p₁^2 + 12 * p₁.
      have H6 : p₁ ∣ p₁^3 + 6 * p₁^2 + 12 * p₁ := by
        have : p₁^3 + 6 * p₁^2 + 12 * p₁ = p₁ * (p₁^2 + 6 * p₁ + 12) := by ring
        rw [this]
        use p₁^2 + 6 * p₁ + 12
      --So it follows that p₁ ∣ 6.
      have H7 : p₁ ∣ 6 := by exact (Nat.dvd_add_iff_right H6).mpr H5
      --Now, the following are the divisors of 6.
      have H8 : p₁ = 1 ∨ p₁ = 2 ∨ p₁ = 3 ∨ p₁ = 6 := by
        have ha : p₁ ∈ (6).divisors := by
          have ⟨b, hb⟩ := H7
          refine Nat.mem_divisors.mpr ?_
          constructor
          exact H7
          linarith
        simp [show (6 : ℕ).divisors = {1, 2, 3, 6} from rfl] at ha
        omega
      --Now obviously p₁ = 1 and p₁ = 6 are impossible.
      have H9 : p₁ ≠ 1 := by exact Nat.Prime.ne_one hp₁
      have H10 : p₁ ≠ 6 := by
        by_contra h
        have : ¬ Nat.Prime 6 := by decide
        rw [h] at hp₁
        subst h htwin
        simp_all only
      --So it follows that p₁ = 2 or p₁ = 3
      --Now since p₂ = p₁ + 2 and p₂ is prime, p₁ = 2 is impossible as well.
      have H11 : p₁ ≠ 2 := by
        by_contra h
        rw [h] at htwin
        simp at htwin
        have : ¬ Nat.Prime 4 := by decide
        rw [htwin] at hp₂
        subst htwin h
        simp_all only
      --Hence p₁ must be 3.
      have H12 : p₁ = 3 := by tauto
      --This means p₂ = 5.
      have H13 : p₂ = 5 := by
        rw [H12] at htwin
        simp at htwin
        exact htwin
      --This means n = 41.
      rw [H12, H13] at hp
      ring_nf at hp
      have : n = 41 := by omega
      exact this
      --Now the converse.
      use 3, 5
      constructor
      decide
      constructor
      decide
      constructor
      rw [H]
      norm_num
      norm_num