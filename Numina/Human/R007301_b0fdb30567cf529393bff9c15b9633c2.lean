import Mathlib

/- 3rd USAMO 1974 Problem 1 p(x) is a polynomial with integral coefficients. Show that there are no solutions to the equations p(a) = b, p(b) = c, p(c) = a, with a, b, c distinct integers. -/
theorem algebra_126114 {p : Polynomial ℤ} (a b c : ℤ) (ha : a ≠ b) (hb : b ≠ c)
    (hc : a ≠ c) (h1 : p.eval a = b) (h2 : p.eval b = c) (h3 : p.eval c = a) :
    False := by
  have h := And.intro ha (And.intro hb hc)
  -- A proof by contradiction. We will show that a = b ∨ b = c ∨ a = c.
  contrapose h
  simp_rw [Decidable.not_and_iff_or_not, not_ne_iff]
  clear h ha hb hc
  -- We have a - b ∣ p.eval a - p.eval b = b - c
  have hab := Polynomial.sub_dvd_eval_sub a b p
  -- We have b - c ∣ p.eval b - p.eval c = c - a
  have hbc := Polynomial.sub_dvd_eval_sub b c p
  -- We have c - a ∣ p.eval c - p.eval a = a - b
  have hca := Polynomial.sub_dvd_eval_sub c a p
  simp_rw [h1, h2, h3] at hab hbc hca
  -- If x ∣ y and y ∣ x then x = y or x = -y.
  have hdvd {x y : ℤ} (h1 : x ∣ y) (h2 : y ∣ x) : x = y ∨ x = -y := by
    rw [← Int.natAbs_eq_natAbs_iff]
    apply Nat.dvd_antisymm <;> rwa [Int.natAbs_dvd_natAbs]
  -- We have a - b ∣ b - c and b - c ∣ c - a ∣ a - b so a - b = b - c or a - b = c - b.
  cases' hdvd hab (Int.dvd_trans hbc hca) with h h
  -- If a - b = b - c then consider
  -- b - c ∣ c - a and c - a ∣ b - c.
  -- So we get b - c = c - a ∨ b - c = a - c.
  · have := hdvd hbc (Int.dvd_trans hca hab)
    -- If b - c = a - c then a = b.
    -- If b - c = c - a and a - b = b - c then we get
    -- -(b - c) = b - a = (b - c) + (c - a) = 2 * (b - c), so b = c.
    omega
  -- If a - b = -(b - c) then a = c.
  · omega