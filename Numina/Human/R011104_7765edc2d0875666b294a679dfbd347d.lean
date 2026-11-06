import Mathlib

/- 2 [

Find all pairs of prime numbers, the difference of the squares of which is a prime number.

# -/
theorem number_theory_218001 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : (p^2 - q^2).Prime) :
    (p, q) = (3, 2) := by
  -- one of p + q or p - q is prime, the other is 1
  rw [Nat.sq_sub_sq, Nat.prime_mul_iff] at h
  rcases h with ⟨hadd, h'⟩ | ⟨hsub, h'⟩
  -- suppose p - q = 1
  · rcases Nat.even_or_odd p with p_even | p_odd
    -- when p = 2 then 2 - q = 1, contradiction
    · rw [Nat.Prime.even_iff hp] at p_even
      rw [p_even, Nat.sub_eq_iff_eq_add, show 2 = 1 + 1 by rfl, Nat.add_right_inj] at h'
      rw [←h'] at hq
      contradiction
      rcases lt_or_ge q 2 with hlt | hge
      · exact hlt.le
      rw [Nat.sub_eq_zero_of_le hge] at h'
      contradiction
    -- when p is odd then q is even so (p, q) = (3, 2)
    · rw [Nat.sub_eq_iff_eq_add] at h'
      have := Odd.add_one p_odd
      rw [h', add_comm 1, add_assoc, Nat.even_add, Nat.Prime.even_iff hq] at this
      simp at this
      rw [this, add_comm] at h'
      rw [h', this]
      rcases lt_or_ge q p with hlt | hge
      · exact hlt.le
      rw [Nat.sub_eq_zero_of_le hge] at h'
      contradiction
  -- p + q = 1 is a contradiction
  rw [Nat.add_eq_one_iff] at h'
  rcases h' with ⟨peq, qeq⟩ | ⟨peq, qeq⟩ <;> { rw [peq] at hp; contradiction }