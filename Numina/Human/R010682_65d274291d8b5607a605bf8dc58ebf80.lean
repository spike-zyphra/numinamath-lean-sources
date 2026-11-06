import Mathlib

/- In an increasing sequence of four positive integers, the first three terms form an arithmetic progression, the last three terms form a geometric progression, and the first and fourth terms differ by 
30
30. Find the sum of the four terms. -/
theorem algebra_98177 (a b c d : ℕ) (h₀ : 0 < a) (h₁ : a < b) (h₂ : b < c) (h₃ : c < d)
(h₄ : ∃ d, b = a + d ∧ c = b + d) (h₅ : ∃ r : ℚ, c = b * r ∧ d = c * r) (h₆ : d - a = 30) :
a + b + c + d = 129 := by
  obtain ⟨t, ⟨ht, hu⟩⟩ := h₄
  obtain ⟨u, ⟨hv, uw⟩⟩ := h₅
  have neq : (↑(a + t) : ℚ) ≠ 0 := by norm_cast; omega
  -- Denote the first term as $a$, and the common difference between the first three terms as $d$. The four numbers thus are in the form $a,\ a+d,\ a+2d,\ \frac{(a + 2d)^2}{a + d}$.
  -- delete variables
  have t1 : b = a + t := by omega
  have t2 : c = a + 2 * t := by omega
  -- now d is more complicated
  have wiu : u = (↑(a + 2 * t) : ℚ) / (↑(a + t) : ℚ) := by
    subst b c
    exact CancelDenoms.cancel_factors_eq_div (id (Eq.symm hv)) neq
  rw [hv, ht, mul_assoc, ←pow_two] at uw
  simp only [Nat.cast_add, wiu, div_pow] at uw
  -- Multiplying out by the denominator,\[(a^2 + 4ad + 4d^2) - a(a + d) = 30(a + d).\]
  rw [pow_two ((↑a : ℚ) + ↑t), mul_comm ((↑a : ℚ) + ↑t), div_mul] at uw
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_self_div_self] at uw
  have att : ((↑a : ℚ) + 2 * ↑t) ^ 2 = ↑d * ((↑a : ℚ) + ↑t) := by
    rw [uw]
    push_cast at neq
    simp only [isUnit_iff_ne_zero, ne_eq, neq, not_false_eq_true, IsUnit.div_mul_cancel]
  rw [pow_two, add_mul, mul_add] at att
  -- This simplifies to $3ad + 4d^2 = 30a + 30d$, which upon rearranging yields $2d(2d - 15) = 3a(10 - d)$.
  have dat : 2 * (↑t : ℚ) * (2 * (↑t : ℚ) - 15) = 3 * (↑a : ℚ) * (10 - (↑t : ℚ)) := by
    qify [(by linarith : d > a)] at h₆
    rw [uw] at h₆
    have tw (a b c : ℚ) (h1 : a = b) : a * c = b * c := by subst a; rfl
    have ga := tw _ _ ((↑a : ℚ) + ↑t) h₆
    push_cast at neq
    ring_nf at ga
    field_simp at ga
    ring_nf
    -- turn into product
    have sta : (-(↑a * ↑t * (↑a + ↑t)) + (↑a * ↑t ^ 2 * 8 - (↑a + ↑t) * ↑a ^ 2) + ↑a ^ 2 * ↑t * 5 + ↑a ^ 3 + ↑t ^ 3 * 4 - (↑a * 30 + ↑t * 30) * (↑a + ↑t) : ℚ) = 0 := by rw [ga]; norm_num
    ring_nf at sta
    have sne : (-(↑a * ↑t * 60) + (↑a * ↑t ^ 2 * 7 - ↑a ^ 2 * 30) + (↑a ^ 2 * ↑t * 3 - ↑t ^ 2 * 30) + ↑t ^ 3 * 4 : ℚ) = ((↑a + ↑t) * (-30 * ↑a - 30 * ↑t + 3 * ↑a * ↑t + 4 * ↑t^2) : ℚ) := by ring
    rw [sne] at sta
    clear sne
    -- a + t ≠ 0, so remove the term from the product
    simp only [neg_mul, mul_eq_zero, neq, false_or] at sta
    linarith
  zify at dat
  have sd : t ≤ 15 := by omega
  -- try all possible values of t
  -- there are only 15 cases, `norm_cast at dat` eliminates 13 out of 15 cases, and only 2 cases need to be solved by `omega`
  have se : t ≠ 0 := by omega
  have sf : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 := by clear * - sd se; omega
  obtain sf | sf | sf | sf | sf | sf | sf | sf | sf | sf | sf | sf | sf | sf | sf := sf <;> subst t <;> norm_num at * <;> norm_cast at dat <;> omega