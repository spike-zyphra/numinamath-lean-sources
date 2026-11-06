import Mathlib

/- ## Task $7 / 70$

We are looking for all prime numbers $p$ that satisfy the equation $c^{3}-c^{2}-11 c-1452=p$ for some positive integer $c$. -/
theorem number_theory_151320 (p : ℕ) (hp : Nat.Prime p) :
    (∃ c: ℤ, c > 0 ∧ c^3 - c^2 - 11 * c - 1452 = p) ↔ p = 433 := by
  constructor <;> intro h
  zify
  have h_p_nonzero := Nat.Prime.ne_zero hp
  obtain ⟨c, ⟨c_pos, c_eq⟩⟩ := h
  -- Every prime number has (except for the order) exactly one representation as a product of two factors
  -- so it is natural to factorize the term c^3 - c^2 - 11c - 1452 intro a product of two factors 
  have h_factorization: (c - 12) * (c^2 + 11*c + 121) = (p: ℤ) := by rw [←c_eq]; ring
  have h_c_quad_pos: c^2 + 11*c + 121 > 1 := by nlinarith
  lift (c^2 + 11*c + 121) to ℕ using (by positivity) with m hm
  have h_c_12_pos: c - 12 ≥ 0 := by
    have: (p: ℤ) > 0 := by positivity
    nlinarith
  lift (c - 12) to ℕ using h_c_12_pos with k hk
  norm_cast at h_factorization
  have h_k_div: k ∣ p := Dvd.intro m h_factorization
  -- Now we need to solve the equations c - 12 = 1 and c^2 + 11c + 121 = 1
  rcases (Nat.dvd_prime hp).mp h_k_div with h_c_val | h_c_val
  -- The first equation yileds c = 13
  replace h_c_val: c = 13 := by omega
  rw [h_c_val] at c_eq
  omega
  -- The second has no real solutions. For positive values of c, we can note that c^2 + 11c + 121 > 0
  rw [h_c_val] at h_factorization
  apply (Nat.mul_eq_left h_p_nonzero).mp at h_factorization
  simp [h_factorization] at h_c_quad_pos
  -- We check that for c = 13, c^3 - c^2 - 11c - 1452 is equal to the prime number 433
  use 13
  constructor
  decide
  rw [h]
  norm_num