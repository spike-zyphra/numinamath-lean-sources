import Mathlib

/- Ed and Sue bike at equal and constant rates.  Similarly, they jog at equal and constant rates, and they swim at equal and constant rates.  Ed covers 7474 kilometers after biking for 22 hours, jogging for 33 hours, and swimming for 44 hours, while Sue covers 9191 kilometers after jogging for 22 hours, swimming for 33 hours, and biking for 44 hours.  Their biking, jogging, and swimming rates are all whole numbers of kilometers per hour.  Find the sum of the squares of Ed's biking, jogging, and swimming rates. -/
theorem algebra_93782 (b j s : ℕ) (h₂ : 0 < j) (h₃ : 0 < s)
(h₄ : 2 * b + 3 * j + 4 * s = 74) (h₅ : 2 * j + 3 * s + 4 * b = 91) :
b^2 + j^2 + s^2 = 314 := by {
  suffices : b = 15 ∧ j = 8 ∧ s = 5
  -- Clearly it suffices to show that (b,j,s) = (15,8,5), as we show now
  rcases this with ⟨hb,hj,hs⟩
  rw [hb,hj,hs]
  norm_num

  -- One solution is to deduce from the equations that 4*j + 5*s = 57. One can then argue that s ≡ 1 [MOD 4] follows and    -- go through the remaining 3 cases. In two of these it turns out that b can not be an integer, from which the claim
  -- follows.
  omega
}