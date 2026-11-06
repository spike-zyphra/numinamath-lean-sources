import Mathlib

/-
PROBLEM: Elmo makes N sandwiches for a fundraiser. For each sandwich he uses B globs of peanut butter at 4 cents per glob 
and J blobs of jam at 5 cents per glob. The cost of the peanut butter and jam to make all the sandwiches is 2.53. Assume that 
B, J and N are all positive integers with N>1. What is the cost of the jam Elmo uses to make the sandwiches?
-/

theorem algebra_97810 {B J N : ℕ} (hB : B > 0) (hJ : J > 0) (hN : N > 1)
(hcost : N*(B * 4 + J * 5) = 253) :
N * J * 5 = 165 := by {
  -- Since N is a divisor of 253 and can not be 1 or 253, it must be 11 or 23
  have hNeqOr : N = 11 ∨ N = 23 := by {
    have hNdvd253 : N ∈ Nat.divisors 253 := by {
      rw [Nat.mem_divisors]
      simp
      use (B*4+J*5)
      symm
      exact hcost
    }
    have h253div : Nat.divisors 253 = {1,11,23,253} := by trivial
    rw [h253div] at hNdvd253
    simp at hNdvd253

    rcases hNdvd253 with hN1 | hN11 | hN23 | hN253
    linarith

    rw [hN11]
    trivial

    rw [hN23]
    trivial

    rw [hN253] at hcost
    linarith
  }

  -- The same holds true for B * 4 + J * 5
  have hBJOr : B * 4 + J * 5 = 11 ∨ B * 4 + J * 5 = 23 := by {
    rcases hNeqOr with hNeq11 | hNeq23
    rw [hNeq11] at hcost
    apply Or.inr
    have h11 : 0 < 11 := by trivial
    apply Nat.eq_of_mul_eq_mul_left h11
    rw [hcost]
    
    rw [hNeq23] at hcost
    apply Or.inl
    have h11 : 0 < 23 := by trivial
    apply Nat.eq_of_mul_eq_mul_left h11
    rw [hcost]
  }

  -- B * 4 + J * 5 can not be 11, because there are no positive integers that satisfy this equation.
  have hBJeq : B * 4 + J * 5 = 23 := by {
    cases hBJOr with
    | inl hBJ11 => {
      have hJle : J ≤ 2 := by linarith
      have hBle : B ≤ 2 := by linarith
      rcases hJle with hJ2 | hJ1 | hJ0
      linarith

      simp at hBJ11
      rcases hBle with hB2 | hB1 | hB0
      trivial
      trivial
      simp at hB0
      linarith

      simp at hJ0
      linarith
    }
    | inr hBJ23 => trivial
  }

  -- Hence N has to be 11
  have hNeq : N = 11 := by {
    rw [hBJeq] at hcost
    linarith
  }
  rw [hNeq]


  -- By checking all the cases, we can see that B * 4 + J * 5 = 23 implies that J = 3 (and B = 2). This implies the claim.
  have hJle : J ≤ 4 := by linarith
  have hBle : B ≤ 5 := by linarith
  have hJeq : J = 3 := by {
    rcases hJle with hJ4 | hJ3 | hJ2 | hJ1 | hJ0
    absurd hBJeq
    linarith

    trivial

    absurd hBJeq
    simp
    rcases hBle with hB5 | hB4 | hB3 | hB2 | hB1 | hB0
    trivial
    trivial
    trivial
    trivial
    trivial
    simp at hB0
    linarith

    absurd hBJeq
    rcases hBle with hB5 | hB4 | hB3 | hB2 | hB1 | hB0
    trivial
    trivial
    trivial
    trivial
    trivial
    simp at hB0
    linarith

    simp at hJ0
    linarith
  }

  rw [hJeq]
}